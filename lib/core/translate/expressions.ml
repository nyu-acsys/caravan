(** OCaml expressions, translated to Raven statements in A-normal form. *)

open Base
open Translate_context
open Proof_terms
open Atomic_proofs
open State.Syntax

let captured_arguments ~at ~values names captured =
  all captured ~f:(fun id ->
      match List.Assoc.find values (Ident.unique_name id) ~equal:String.equal with
      | Some value -> Ok value
      | None ->
          begin match State.name_in names id with
          | Some variable -> Ok (R.Expr.var ~loc:(loc at) (name ~loc:(loc at) variable))
          | None -> error at (Printf.sprintf "%s is not in scope here" (Ident.name id))
          end)

let constructor_value ctx ~at ~result_type data constructor arguments =
  let value =
    R.Expr.call ~loc:(loc at)
      (Datatypes.ctor_name ~loc:(loc at) data constructor)
      arguments
  in
  if List.is_empty data.Datatypes.parameters then State.return value
  else
    let+ typ = State.typ ctx ~at result_type in
    R.Expr.annotated value typ

let polymorphic_ordering ctx path (args : Typedtree.expression list) =
  match stdlib_name path with
  | Some ("<" | ">" | "<=" | ">=" | "compare") ->
      List.exists args ~f:(fun argument ->
          List.exists
            (Polymorphic_functions.all_variables
               (Datatypes.expand ctx.given.types argument.exp_type))
            ~f:(fun variable ->
              Option.is_some (Datatypes.find_variable ctx.given.types variable)))
  | _ -> false

(** The statements evaluating [e], and the value of [e] after them; [tail] if the value is
    the function's result. *)
let rec expr ?(tail = false) ?(continue_state = false) ?(keep_scope = false)
    (ctx : context) (e : Typedtree.expression) : (R.Stmt.t list * R.Expr.t) State.t =
  let* (s : State.state) = State.get in
  let incoming = s.carried.proof_state and covered = s.carried.return_covered in
  let incoming_names = s.names.scope in
  let key = (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum) in
  let adapter = List.Assoc.find ctx.given.return_proofs key ~equal:Poly.equal in
  let* () =
    State.of_result
      begin match adapter with
      | Some a when not tail ->
          error a.loc "Ghost.returns must follow a normal tail expression"
      | Some a when covered ->
          error a.loc "This return path has more than one Ghost.returns annotation"
      | _ -> Ok ()
      end
  in
  let return_covered = covered || Option.is_some adapter in
  let* () = State.modify_carried (fun c -> { c with return_covered }) in
  let tail_container =
    match e.exp_desc with
    | Texp_let _ | Texp_sequence _ | Texp_match _ -> true
    | Texp_ifthenelse (_, _, Some _) -> true
    | _ -> false
  in
  let* () =
    if
      tail && (not return_covered) && (not tail_container)
      && not (List.is_empty s.carried.ghost_returns)
    then
      State.of_result
        (error e.exp_loc "A normal return with ghost results needs Ghost.returns")
    else State.return ()
  in
  let* statements, value = expr_body ~tail ~keep_scope ctx e in
  let* finish =
    match adapter with
    | None -> State.return []
    | Some a -> return_proof ctx a ~result_type:e.exp_type ~result:value
  in
  let* stateful = State.of_result (stateful_access ctx.given.access_proofs e) in
  let* () =
    if not (continue_state && stateful) then
      State.modify_carried (fun c -> { c with proof_state = incoming })
    else State.return ()
  in
  let* () = if not keep_scope then State.set_scope incoming_names else State.return () in
  let+ () = State.modify_carried (fun c -> { c with return_covered = covered }) in
  (statements @ finish, value)

and expr_body ~tail ~keep_scope (ctx : context) (e : Typedtree.expression) :
    (R.Stmt.t list * R.Expr.t) State.t =
  let at = e.exp_loc in
  let l = loc at in
  match e.exp_desc with
  | Texp_ident (Pident id, _, _) -> (
      let* x = State.find_name id in
      match x with
      | Some x -> State.return ([], R.Expr.var ~loc:l (name ~loc:l x))
      | None -> State.of_result (unsupported at "A function used as a value"))
  | Texp_ident (path, _, _) -> (
      let* path = State.of_result (Source.normalize_value_path e.exp_env ~at path) in
      match Path_bindings.member ctx.given.libraries path with
      | Some member ->
          State.return ([], R.Expr.call ~loc:l (Qualified_name.raven ~loc:l member) [])
      | None ->
          begin match stdlib_name path with
          | Some "max_int" -> State.return ([], R.Expr.int ~loc:l Prelude.max_int)
          | Some "min_int" -> State.return ([], R.Expr.int ~loc:l Prelude.min_int)
          | _ -> State.of_result (unsupported at "This identifier")
          end)
  | Texp_constant (Const_int n) -> State.return ([], R.Expr.int ~loc:l n)
  | Texp_constant _ -> State.of_result (unsupported at "This constant")
  | Texp_unreachable ->
      let* typ = State.typ ctx ~at e.exp_type in
      let+ x = State.fresh "unreachable" in
      ( R.Stmt.assert_ ~loc:l (R.Spec.make (R.Expr.bool ~loc:l false))
        :: R.Stmt.local ~loc:l ~typ (ident ~loc:l x),
        R.Expr.var ~loc:l (name ~loc:l x) )
  | Texp_construct ({ txt = Lident "true"; _ }, _, []) ->
      State.return ([], R.Expr.bool ~loc:l true)
  | Texp_construct ({ txt = Lident "false"; _ }, _, []) ->
      State.return ([], R.Expr.bool ~loc:l false)
  | Texp_construct ({ txt = Lident "()"; _ }, _, []) ->
      State.return ([], unit_value ~loc:l)
  | Texp_construct (_, cstr, args) ->
      begin match occurrence_constructor ctx.given.types e.exp_type cstr with
      | None -> State.of_result (unsupported at "This constructor")
      | Some (d, c) ->
          let* stmts, values = operands ctx args in
          let* named =
            State.all (List.zip_exn args values) ~f:(fun (arg, value) ->
                established ctx arg value)
          in
          let+ value =
            match shared_exception ctx c with
            (* The application's own exception, in a functor body it shares. *)
            | Some app ->
                State.return
                  (shared_exception_call ~loc:l app "make" c (List.map named ~f:snd))
            | None ->
                constructor_value ctx ~at ~result_type:e.exp_type d c
                  (List.map named ~f:snd)
          in
          (stmts @ List.concat_map named ~f:fst, value)
      end
  | Texp_tuple components ->
      let+ stmts, components = operands ctx (List.map components ~f:snd) in
      (stmts, R.Expr.tuple ~loc:l components)
  | Texp_record { fields; extended_expression = None; _ } ->
      let fields = Array.to_list fields in
      let* values =
        State.of_result
          (all fields ~f:(fun (label, def) ->
               match (def : Typedtree.record_label_definition) with
               | Overridden (_, e) -> Ok (label, e)
               | Kept _ -> unsupported at "This record"))
      in
      let* stmts, args = operands ctx (List.map values ~f:snd) in
      let label, _ = List.hd_exn fields in
      begin match
        Option.first_some
          (Datatypes.instantiated ctx.given.types e.exp_type)
          (Datatypes.find_label ctx.given.types label)
      with
      | Some { heap = Some _; _ } ->
          let* typ = State.typ ctx ~at e.exp_type in
          let* fields =
            State.all values ~f:(fun (label, _) ->
                let+ field = State.field_of_label ctx.given ~at label in
                fst (Option.value_exn field))
          in
          let* x = State.fresh "tmp" in
          let* views, view_args = view_allocation ctx ~loc:l fields in
          let+ explicit = allocation_initializers ctx e in
          let init =
            R.Stmt.new_rhs
              (List.map2_exn fields args ~f:(fun f v -> (qualified_name ~loc:l f, Some v))
              @ view_args @ explicit)
          in
          ( stmts @ views @ R.Stmt.local ~loc:l ~typ ~init (ident ~loc:l x),
            R.Expr.var ~loc:l (name ~loc:l x) )
      | Some ({ ctors = [ c ]; _ } as d) ->
          let+ value = constructor_value ctx ~at ~result_type:e.exp_type d c args in
          (stmts, value)
      | _ -> State.of_result (unsupported at "This record")
      end
  | Texp_record _ -> State.of_result (unsupported at "A record copied with changes")
  | Texp_field (record, _, label) -> begin
      let* stmts, v = expr ctx record in
      let* field = State.field_of_label ctx.given ~at label in
      match field with
      | Some (field, true) ->
          let+ reading, value =
            State.ordinary_read ctx.given ~at ~field ~elt:e.exp_type v
          in
          (stmts @ reading, value)
      | Some (field, false) -> begin
          let value = R.Expr.field ~loc:l v (qualified_name ~loc:l field) in
          match Datatypes.admissible ~loc:l ctx.given.types e.exp_type value with
          | None -> State.return (stmts, value)
          | Some _ ->
              let* typ = State.typ ctx ~at e.exp_type in
              let* () = State.note_domain ctx.given.types e.exp_type in
              let+ x = State.fresh "tmp" in
              ( stmts
                @ R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs value) (ident ~loc:l x)
                @ assert_admissible ctx ~loc:l e.exp_type x,
                R.Expr.var ~loc:l (name ~loc:l x) )
        end
      | None -> State.of_result (unsupported at "This field")
    end
  | Texp_setfield (record, _, label, value) -> begin
      let* value_stmts, value = expr ctx value in
      let* record_stmts, record = expr ctx record in
      let* field = State.field_of_label ctx.given ~at label in
      match field with
      | Some (field, true) ->
          let+ writing =
            State.ordinary_write ctx.given ~at ~field ~elt:label.lbl_arg record value
          in
          (value_stmts @ record_stmts @ [ writing ], unit_value ~loc:l)
      | _ -> State.of_result (unsupported at "This field")
    end
  | Texp_match (scrutinee, cases, [], partial)
    when List.exists cases ~f:(fun (c : Typedtree.computation Typedtree.case) ->
             Option.is_some (snd (Typedtree.split_pattern c.c_lhs))) ->
      (* The scrutinee is protected; its value's cases are not. *)
      let* cases =
        State.of_result
          (all cases ~f:(fun (c : Typedtree.computation Typedtree.case) ->
               match (Typedtree.split_pattern c.c_lhs, c.c_guard) with
               | _, Some guard -> unsupported guard.exp_loc "A guard"
               | (Some p, None), None -> Ok (`Value (p, c.c_rhs))
               | (None, Some p), None -> Ok (`Exception (p, c.c_rhs))
               | (_, _), None -> unsupported c.c_lhs.pat_loc "A value and exception case"))
      in
      let values =
        List.filter_map cases ~f:(function `Value c -> Some c | `Exception _ -> None)
      and exceptions =
        List.filter_map cases ~f:(function `Exception c -> Some c | `Value _ -> None)
      in
      let* typ = State.typ ctx ~at:scrutinee.exp_loc scrutinee.exp_type in
      let* x = State.fresh "scrutinee" in
      let v = R.Expr.var ~loc:l (name ~loc:l x) in
      let+ stmts, value =
        handled ctx ~at ~tail e ~cases:exceptions
          ~protected:(fun _ ->
            let+ stmts, s = expr ctx scrutinee in
            stmts @ [ assign (x, l) s ])
          ~normal:(fun target ->
            match_cases ~tail ctx ~at v values
              ~total:(match partial with Total -> true | Partial -> false)
              target)
      in
      (R.Stmt.local ~loc:l ~const:false ~typ (ident ~loc:l x) @ stmts, value)
  | Texp_match ({ exp_desc = Texp_ident (Pident id, _, _); _ }, cases, [], _)
    when Option.is_some
           (specialized_case ctx ~scrutinee:(Ident.name id) cases
              ~constructors:(fun (c : Typedtree.computation Typedtree.case) ->
                match Typedtree.split_pattern c.c_lhs with
                | Some p, None -> Exceptions.matched_constructors p
                | _ -> Some [])) ->
      (* In a copy for a witness's constructor, a match on the witness is its case. *)
      let case =
        Option.value_exn
          (specialized_case ctx ~scrutinee:(Ident.name id) cases
             ~constructors:(fun (c : Typedtree.computation Typedtree.case) ->
               match Typedtree.split_pattern c.c_lhs with
               | Some p, None -> Exceptions.matched_constructors p
               | _ -> Some []))
      in
      expr ~tail ctx case.c_rhs
  | Texp_match (scrutinee, cases, [], partial) ->
      let* read = is_read_value scrutinee in
      let* scrutinee_stmts, v = expr ctx scrutinee in
      (* The cases read the scrutinee repeatedly, so it is named unless it is a variable. *)
      let* naming, v =
        match scrutinee.exp_desc with
        | Texp_ident (Pident _, _, _) -> State.return ([], v)
        | _ ->
            let* typ = State.typ ctx ~at:scrutinee.exp_loc scrutinee.exp_type in
            let+ x = State.fresh "scrutinee" in
            ( R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs v) (ident ~loc:l x),
              R.Expr.var ~loc:l (name ~loc:l x) )
      in
      let* cases =
        State.of_result
          (all cases ~f:(fun (c : Typedtree.computation Typedtree.case) ->
               match (Typedtree.split_pattern c.c_lhs, c.c_guard) with
               | (Some p, None), None -> Ok (p, c.c_rhs)
               | _, Some guard -> unsupported guard.exp_loc "A guard"
               | _ -> unsupported c.c_lhs.pat_loc "An exception case"))
      in
      let total = match partial with Total -> true | Partial -> false in
      let* arm =
        State.of_result
          (Witnesses.arms ctx.given.types ~at ~current:ctx.given.current_polymorphic
             ~scrutinee:scrutinee.exp_type ~result:e.exp_type cases)
      in
      (* A match on the value of a read that left the atomic update open closes it. *)
      let* state = au_state in
      let commits =
        match state with
        | Some (On_read c | Collecting c) when read ->
            Some (case_commits c (List.map cases ~f:fst))
        | _ -> None
      in
      let+ stmts =
        branch ctx e (fun target ->
            match_cases ?commits ?arm ~tail ctx ~at v cases ~total target)
      in
      (scrutinee_stmts @ naming @ fst stmts, snd stmts)
  | Texp_match (_, _, _ :: _, _) -> State.of_result (unsupported at "An effect handler")
  | Texp_try (body, handlers, []) ->
      let* cases =
        State.of_result
          (all handlers ~f:(fun (c : Typedtree.value Typedtree.case) ->
               match c.c_guard with
               | Some guard -> unsupported guard.exp_loc "A guard"
               | None -> Ok (c.c_lhs, c.c_rhs)))
      in
      handled ctx ~at ~tail e ~cases
        ~protected:(fun target ->
          let+ stmts, v = expr ctx body in
          stmts @ Option.value_map target ~default:[] ~f:(fun t -> [ assign t v ]))
        ~normal:(fun _ -> State.return [])
  | Texp_try _ -> State.of_result (unsupported at "An effect handler")
  | Texp_apply _ when Option.is_some (Exceptions.raised_argument e) ->
      let argument = Option.value_exn (Exceptions.raised_argument e) in
      let* stmts, v = expr ctx argument in
      let* caught = State.gets (fun (s : State.state) -> s.carried.caught) in
      let set =
        match
          ( Exceptions.named ~key:(Exceptions.key ctx.given.types) argument,
            argument.exp_desc )
        with
        | Some name, _ -> State.Raises [ name ]
        | None, Texp_ident (Pident id, _, _) ->
            (* Re-raising what a handler caught. *)
            Option.value
              (List.Assoc.find caught id ~equal:Ident.same)
              ~default:State.Raises_any
        | None, _ -> State.Raises_any
      in
      let* outcome = State.typ ctx ~at outcome_type in
      (* Leaving a function with an atomic contract commits its update with the exception:
         the step before linearized it. *)
      let* (carried : State.carried) = State.gets (fun (s : State.state) -> s.carried) in
      let* commit =
        match (ctx.au, carried.handlers) with
        | Some au, [] -> (
            let* state = au_state in
            match state with
            | Some Committing ->
                let* () = put_au_state Committed in
                let result =
                  match (au.has_result, carried.exit) with
                  | true, Some { results = r :: _; _ } -> r
                  | _ -> R.Expr.tuple ~loc:l []
                in
                au.close Commit ~value:result
                  ~outcome:
                    (Raised
                       (v, Exceptions.named ~key:(Exceptions.key ctx.given.types) argument))
            | _ ->
                State.of_result
                  (error at
                     "This raise may leave the function before a step linearizes it, or \
                      after it linearized returning: annotate the step that linearizes \
                      it by raising, as (*@ returning [] -> commit *)"))
        | _ -> State.return []
      in
      let* leave =
        propagate ~at ~certain:true ~typ:outcome (raised_exception ~loc:l outcome v) set
      in
      let leave = commit @ leave in
      (* The raise's value, which no code after it reads. *)
      if is_unit e.exp_type then State.return (stmts @ leave, unit_value ~loc:l)
      else
        let* typ = State.typ ctx ~at e.exp_type in
        let+ x = State.fresh "unreachable" in
        ( stmts @ leave @ R.Stmt.local ~loc:l ~typ (ident ~loc:l x),
          R.Expr.var ~loc:l (name ~loc:l x) )
  | Texp_apply (({ exp_desc = Texp_ident (path, _, declaration); _ } as callee), args) ->
      let* args = State.of_result (plain_args ~at args) in
      apply ctx e path declaration callee.exp_type args
  | Texp_apply _ -> State.of_result (unsupported at "This application")
  | Texp_ifthenelse (c, e1, e2) ->
      let* polarity = cas_polarity c in
      let* c_stmts, c = expr ctx c in
      let+ stmts =
        branch ctx e (fun target -> conditional ctx ~at ?polarity ~tail c e1 e2 target)
      in
      (c_stmts @ fst stmts, snd stmts)
  | Texp_let (_, [ { vb_pat = { pat_desc = Tpat_var (id, _, _); _ }; _ } ], rest)
    when Path_bindings.mem ctx.given.functions (Path.Pident id) ->
      (* A local function, lifted to the top level. *)
      expr ~tail ~keep_scope ctx rest
  | Texp_let (Nonrecursive, bindings, body) ->
      (* The bound expressions are evaluated before any of their variables is bound. *)
      let* evaluated =
        State.all bindings ~f:(fun (vb : Typedtree.value_binding) ->
            let* polarity = cas_polarity vb.vb_expr in
            let* read = is_read_value vb.vb_expr in
            let* stmts, v =
              expr ~continue_state:(List.length bindings = 1) ctx vb.vb_expr
            in
            let+ () =
              match (polarity, vb.vb_pat.pat_desc) with
              | Some p, Tpat_var (id, _, _) -> record_cas_result id p
              | None, Tpat_var (id, _, _) when read -> record_read_result id
              | _ -> State.return ()
            in
            (vb, stmts, v))
      in
      let* defs =
        State.all evaluated ~f:(fun ((vb : Typedtree.value_binding), _, v) ->
            let* reading, cond, binds = pattern ctx vb.vb_pat v in
            match cond with
            | Some _ ->
                State.of_result
                  (unsupported vb.vb_pat.pat_loc "A refutable pattern in a let binding")
            | None ->
                let+ defs =
                  State.all binds ~f:(fun (id, value, t) ->
                      let* typ = State.typ ctx ~at t in
                      let* () = State.note_domain ctx.given.types t in
                      let+ x = State.bind_name ~typ:t id in
                      R.Stmt.local ~loc:l ~const:true ~typ ~init:(R.Stmt.expr_rhs value)
                        (ident ~loc:l x)
                      @ assert_admissible ctx ~loc:l t x)
                in
                reading @ List.concat defs)
      in
      let last = List.last_exn bindings in
      let* ghost =
        ghost ctx ~after:last.vb_expr.exp_loc.loc_end ~before:body.exp_loc.loc_start
      in
      let+ body_stmts, body = expr ~tail ~keep_scope ctx body in
      ( List.concat_map evaluated ~f:(fun (_, stmts, _) -> stmts)
        @ List.concat defs @ ghost @ body_stmts,
        body )
  | Texp_let (Recursive, _, _) ->
      State.of_result (unsupported at "A local recursive function")
  | Texp_sequence (e1, e2) ->
      let* stmts1, _ = expr ~continue_state:true ctx e1 in
      let* ghost = ghost ctx ~after:e1.exp_loc.loc_end ~before:e2.exp_loc.loc_start in
      let+ stmts2, v = expr ~tail ~keep_scope ctx e2 in
      (stmts1 @ ghost @ stmts2, v)
  | Texp_while (cond, body) ->
      let* () = no_loop_before_linearizing ~at in
      let* spec = State.of_result (loop_spec ctx ~after:cond.exp_loc body) in
      let* c_stmts, c = expr ctx cond in
      let* x = State.fresh "continue" in
      (* A condition that needs statements, as reads, is evaluated before the loop and at the
         end of each iteration, into [x]; the invariant relates [x] to the values it owns,
         if the condition can be expressed in them. *)
      let relation reads =
        if List.is_empty c_stmts then State.return None
        else
          let+ c = State.attempt (pure ~reads ctx ~funcs:Path_bindings.empty [] cond) in
          match c with
          | Ok c -> Some (R.Expr.binary ~loc:l Eq (R.Expr.var ~loc:l (name ~loc:l x)) c)
          | Error _ -> None
      in
      (* A loop that may raise stops once it has, and then propagates the exception. *)
      let* raising = loop_raising ctx ~at ~spec (Some cond) body in
      let guard = Option.map raising ~f:(fun (_, _, _, g, _) -> g) in
      let decl, exceptional =
        Option.value_map raising ~default:([], []) ~f:(fun (d, _, _, _, x) -> (d, x))
      in
      let unraised c =
        Option.value_map guard ~default:c ~f:(fun g -> R.Expr.binary ~loc:l And c g)
      in
      let* invariants = loop_invariants ?guard ctx ~at spec ~relation in
      let invariants = invariants @ exceptional in
      let target = (x, l) in
      let* body_stmts, reaching =
        in_loop raising (fun () ->
            let* body_stmts, _ = expr ctx body in
            if List.is_empty c_stmts then State.return body_stmts
            else
              let+ c_stmts', c' = expr ctx cond in
              body_stmts @ c_stmts' @ [ assign target c' ])
      in
      let+ propagation =
        match raising with
        | None -> State.return []
        | Some (_, outcome, typ, _, _) ->
            propagate ~at ~certain:false ~typ outcome reaching
      in
      if List.is_empty c_stmts then
        ( decl @ [ R.Stmt.while_ ~loc:l ~invariants (unraised c) body_stmts ] @ propagation,
          unit_value ~loc:l )
      else
        ( c_stmts @ decl
          @ R.Stmt.local ~loc:l ~const:false ~typ:(R.Type.bool ~loc:l) (ident ~loc:l x)
          @ [
              assign target c;
              R.Stmt.while_ ~loc:l ~invariants
                (unraised (R.Expr.var ~loc:l (name ~loc:l x)))
                body_stmts;
            ]
          @ propagation,
          unit_value ~loc:l )
  | Texp_for (id, _, lo, hi, direction, body) ->
      let* () = no_loop_before_linearizing ~at in
      let* spec = State.of_result (loop_spec ctx ~after:hi.exp_loc body) in
      let* lo_stmts, lo = expr ctx lo in
      let* hi_stmts, hi = expr ctx hi in
      let int = R.Type.int ~loc:l in
      (* A bound, evaluated once into a variable, which the invariant says it equals, as the
         value is an expression of immutable variables. *)
      let bound base v =
        let+ x = State.fresh base in
        let var = R.Expr.var ~loc:l (name ~loc:l x) in
        ( R.Stmt.local ~loc:l ~typ:int ~init:(R.Stmt.expr_rhs v) (ident ~loc:l x),
          var,
          R.Spec.make (R.Expr.binary ~loc:l Eq var v) )
      in
      let* lo_def, lo, lo_value = bound "first" lo in
      let* hi_def, hi, hi_value = bound "last" hi in
      let* i = State.bind_name ~typ:Predef.type_int id in
      let iv = R.Expr.var ~loc:l (name ~loc:l i) in
      let* raising = loop_raising ctx ~at ~spec None body in
      let guard = Option.map raising ~f:(fun (_, _, _, g, _) -> g) in
      let decl, exceptional =
        Option.value_map raising ~default:([], []) ~f:(fun (d, _, _, _, x) -> (d, x))
      in
      let* invariants =
        loop_invariants ~counter:i ?guard ctx ~at spec ~relation:(fun _ ->
            State.return None)
      in
      let invariants = invariants @ exceptional in
      let bin op a b = R.Expr.binary ~loc:l op a b in
      let one = R.Expr.int ~loc:l 1 in
      let test, step, beyond =
        match direction with
        | Upto -> (bin Leq iv hi, bin Plus iv one, bin Plus hi one)
        | Downto -> (bin Geq iv hi, bin Minus iv one, bin Minus hi one)
      in
      (* The counter stays between the first value and one beyond the last. *)
      let range =
        match direction with
        | Upto -> bin And (bin Leq lo iv) (bin Or (bin Leq iv beyond) (bin Eq iv lo))
        | Downto -> bin And (bin Geq lo iv) (bin Or (bin Geq iv beyond) (bin Eq iv lo))
      in
      let* body_stmts, reaching =
        in_loop raising (fun () ->
            let+ body_stmts, _ = expr ctx body in
            body_stmts @ [ assign (i, l) step ])
      in
      let+ propagation =
        match raising with
        | None -> State.return []
        | Some (_, outcome, typ, _, _) ->
            propagate ~at ~certain:false ~typ outcome reaching
      in
      let test = Option.value_map guard ~default:test ~f:(bin And test) in
      ( lo_stmts @ hi_stmts @ lo_def @ hi_def @ decl
        @ R.Stmt.local ~loc:l ~const:false ~typ:int ~init:(R.Stmt.expr_rhs lo)
            (ident ~loc:l i)
        @ [
            R.Stmt.while_ ~loc:l
              ~invariants:(R.Spec.make range :: lo_value :: hi_value :: invariants)
              test body_stmts;
          ]
        @ propagation,
        unit_value ~loc:l )
  | Texp_assert (c, _) ->
      let* stmts, c = expr ctx c in
      let statements = stmts @ [ R.Stmt.assert_ ~loc:l (R.Spec.make c) ] in
      if is_unit e.exp_type then State.return (statements, unit_value ~loc:l)
      else
        let* typ = State.typ ctx ~at e.exp_type in
        let+ result = State.fresh "unreachable" in
        ( statements @ R.Stmt.local ~loc:l ~typ (ident ~loc:l result),
          R.Expr.var ~loc:l (name ~loc:l result) )
  | _ -> State.of_result (unsupported at "This expression")

(** The application of the function at [path] to [args], in [e]. *)
and apply ctx (e : Typedtree.expression) (path : Path.t) declaration occurrence
    (args : Typedtree.expression list) =
  let at = e.exp_loc in
  let l = loc at in
  let contents (r : Typedtree.expression) =
    match Datatypes.desc ctx.given.types r.exp_type with
    | Tconstr (_, [ elt ], _) -> State.ref_field ctx.given ~at elt
    | _ -> State.of_result (unsupported at "This reference")
  in
  (* The value of the field [field] of the reference [r], read into a variable. *)
  let read r field typ_of = State.ordinary_read ctx.given ~at ~field ~elt:typ_of r in
  match (stdlib_name path, args) with
  | _ when Option.is_some (atomic_name path) ->
      atomic ctx e (Option.value_exn (atomic_name path)) args
  | Some "ref", [ v ] ->
      let allocation =
        Datatypes.allocation_tag ~prefix:"ref_" ~suffix:"_contents" ctx.given.types
          v.exp_type
      in
      let* field = State.ref_field ctx.given ~at v.exp_type in
      let* stmts, v = expr ctx v in
      let* x = State.fresh "tmp" in
      let* views, view_args = view_allocation ctx ~loc:l (Option.to_list allocation) in
      let+ explicit = allocation_initializers ctx e in
      let init =
        R.Stmt.new_rhs ((qualified_name ~loc:l field, Some v) :: (view_args @ explicit))
      in
      ( stmts @ views @ R.Stmt.local ~loc:l ~typ:(R.Type.ref ~loc:l) ~init (ident ~loc:l x),
        R.Expr.var ~loc:l (name ~loc:l x) )
  | Some "!", [ r ] ->
      let* field = contents r in
      let* stmts, r = expr ctx r in
      let+ reading, v = read r field e.exp_type in
      (stmts @ reading, v)
  | Some ":=", [ r; v ] ->
      let* field = contents r in
      let elt = v.exp_type in
      let* v_stmts, v = expr ctx v in
      let* r_stmts, r = expr ctx r in
      let+ writing = State.ordinary_write ctx.given ~at ~field ~elt r v in
      (v_stmts @ r_stmts @ [ writing ], unit_value ~loc:l)
  | Some (("incr" | "decr") as op), [ r ] ->
      let* field = contents r in
      let* stmts, r = expr ctx r in
      let int_type = Predef.type_int in
      let* reading, v = read r field int_type in
      let binop : R.Expr.binop = if String.equal op "incr" then Plus else Minus in
      let v' = R.Expr.binary ~loc:l binop v (R.Expr.int ~loc:l 1) in
      let what = if String.equal op "incr" then "increment" else "decrement" in
      let* writing = State.ordinary_write ctx.given ~at ~field ~elt:int_type r v' in
      let+ overflow = State.no_overflow ~at what v' in
      (stmts @ reading @ [ overflow; writing ], unit_value ~loc:l)
  | _ -> apply_operator ctx e path declaration occurrence args

(** The application of [Atomic.op] to [args], in [e]. *)
and atomic ctx (e : Typedtree.expression) op (args : Typedtree.expression list) =
  let at = e.exp_loc in
  let l = loc at in
  let element (t : Types.type_expr) =
    match Datatypes.desc ctx.given.types t with
    | Tconstr (_, [ elt ], _) -> State.return elt
    | _ -> State.of_result (unsupported at "This atomic")
  in
  (* How the step linearizes the function: as its annotation says, or by default. *)
  let* annotation = State.of_result (linearization ctx e) in
  let how default =
    match (annotation, default) with
    | None, _ -> State.return default
    | Some (S.Performs a), _ ->
        begin match named_action ctx a with
        | Some performed ->
            let+ () = set_performing performed in
            default
        | None ->
            State.of_result
              (error a.pid_loc (Printf.sprintf "There is no action %s" a.pid_str))
        end
    | Some S.Commit, _ -> State.return `Commit
    | Some (Returning ({ pat_desc = Pconstr (Qid c, _); _ }, Commits)), `Abort ->
        State.return (`Returning c.pid_str)
    | Some (Returning (p, Commits)), `Abort ->
        State.of_result
          (unsupported p.pat_loc "A pattern other than a constructor, after returning,")
    | Some (Returning (p, o)), `Abort -> State.return (`Decide (p, o))
    | Some (Returning (p, _)), _ ->
        State.of_result (error p.pat_loc "Only a read can linearize by its value")
  in
  (* The result of [f] applied to the atomic and [args], in a variable, a step that
     linearizes the function by default as [default] says. *)
  let result ?(default = `Commit) ?op ~contents f atomic args =
    let* typ = State.typ ctx ~at e.exp_type in
    let* x = State.fresh "tmp" in
    let v = R.Expr.var ~loc:l (name ~loc:l x) in
    let init =
      R.Stmt.expr_rhs (R.Expr.call ~loc:l (qualified_name ~loc:l f) (atomic :: args))
    in
    let* how = how default in
    let step = Option.map op ~f:(fun (op, field) -> (op, field, atomic, args, v)) in
    let+ step =
      linearize ?step ~value:v ~access_type:e.exp_type ~contents ctx ~at how
        (R.Stmt.local ~loc:l ~typ ~init (ident ~loc:l x))
    in
    (step, v)
  in
  let* elt =
    match args with
    | a :: _ when not (String.is_prefix op ~prefix:"make") -> element a.exp_type
    | _ -> element e.exp_type
  in
  let* field = State.atomic_field ctx.given ~at elt in
  let* nested = State.of_result (nested_stateful_read ctx.given.access_proofs e) in
  let* stmts, values =
    match nested with
    | Some argument ->
        let+ stmts, value = expr ~continue_state:true ctx argument in
        (stmts, [ value ])
    | None -> operands ctx args
  in
  let primitive op = State.primitive ctx.given ~at elt op in
  match (op, values) with
  | ("make" | "make_contended"), [ v ] ->
      let allocation =
        Datatypes.allocation_tag ~prefix:"atomic_" ~suffix:"" ctx.given.types elt
      in
      let* x = State.fresh "tmp" in
      let* views, view_args = view_allocation ctx ~loc:l (Option.to_list allocation) in
      let+ explicit = allocation_initializers ctx e in
      let init =
        R.Stmt.new_rhs ((qualified_name ~loc:l field, Some v) :: (view_args @ explicit))
      in
      ( stmts @ views @ R.Stmt.local ~loc:l ~typ:(R.Type.ref ~loc:l) ~init (ident ~loc:l x),
        R.Expr.var ~loc:l (name ~loc:l x) )
  | "get", [ a ] ->
      let* typ = State.typ ctx ~at e.exp_type in
      let* x = State.fresh "tmp" in
      let read = R.Stmt.expr_rhs (R.Expr.field ~loc:l a (qualified_name ~loc:l field)) in
      let* how = how `Abort in
      let value = R.Expr.var ~loc:l (name ~loc:l x) in
      let* step =
        linearize ~value ~access_type:e.exp_type ~contents:elt ctx ~at how
          (R.Stmt.local ~loc:l ~typ ~init:read (ident ~loc:l x))
      in
      let+ () = record_read ctx ~atomic:a value in
      (stmts @ step, R.Expr.var ~loc:l (name ~loc:l x))
  | "set", [ a; v ] ->
      let* how = how `Commit in
      let+ step =
        linearize ~value:(unit_value ~loc:l) ~access_type:e.exp_type ~contents:elt ctx ~at
          how
          [ write ~loc:l a field v ]
      in
      (stmts @ step, unit_value ~loc:l)
  | "exchange", [ a; v ] ->
      let* f = primitive Exchange in
      let+ reading, r = result ~contents:elt f a [ v ] in
      (stmts @ reading, r)
  | "compare_and_set", [ a; old_val; new_val ] ->
      let* f = primitive Compare_and_set in
      let+ reading, r =
        result ~default:`Cas ~op:("compare_and_set", field) ~contents:elt f a
          [ old_val; new_val ]
      in
      (stmts @ reading, r)
  | "fetch_and_add", [ a; n ] ->
      let* f = primitive Fetch_and_add in
      let+ reading, r = result ~contents:elt f a [ n ] in
      (stmts @ reading, r)
  | (("incr" | "decr") as op), [ a ] ->
      let* f = primitive Fetch_and_add in
      let* x = State.fresh "tmp" in
      let n = R.Expr.int ~loc:l (if String.equal op "incr" then 1 else -1) in
      let init = R.Stmt.expr_rhs (R.Expr.call ~loc:l (name ~loc:l f) [ a; n ]) in
      let* how = how `Commit in
      let+ step =
        linearize ~value:(unit_value ~loc:l) ~access_type:e.exp_type ~contents:elt ctx ~at
          how
          (R.Stmt.local ~loc:l ~typ:(R.Type.int ~loc:l) ~init (ident ~loc:l x))
      in
      (stmts @ step, unit_value ~loc:l)
  | _ -> State.of_result (unsupported at ("Atomic." ^ op))

(** The application of the operator or function at [path] to [args], in [e]. *)
and apply_operator ctx (e : Typedtree.expression) (path : Path.t) declaration occurrence
    (args : Typedtree.expression list) =
  let at = e.exp_loc in
  let l = loc at in
  if polymorphic_ordering ctx path args then
    State.of_result (unsupported at "Ordering on polymorphic values")
  else
    match (binop_of_path path, unop_of_path path, args) with
    | Some (Eq | Neq), _, [ a; b ] when runtime_structural_equality_unsafe ctx path a b ->
        State.of_result
          (error at "Structural equality on values containing references is unsupported")
    | Some ((And | Or) as op), _, [ a; b ] ->
        (* The right operand is evaluated only if the left one does not decide. *)
        let* a_stmts, a = expr ctx a in
        let* before = get_path in
        let* b_stmts, b = expr ctx b in
        (* The snapshots that the right operand takes are on one path only. *)
        let* () =
          modify_path (fun path ->
              {
                path with
                snapshots = common_snapshots [ before.snapshots; path.snapshots ];
                positions = before.positions;
              })
        in
        if List.is_empty b_stmts then State.return (a_stmts, R.Expr.binary ~loc:l op a b)
        else
          let then_, else_ =
            match op with And -> (`Rhs, `Value false) | _ -> (`Value true, `Rhs)
          in
          let* before = pending_count in
          let* stmts, v =
            branch ctx e (fun target ->
                let* target =
                  State.of_result
                    (Report.expect ~at:e.exp_loc
                       "The variable of a Boolean operator's value" target)
                in
                let arm = function
                  | `Rhs -> nest (b_stmts @ [ assign target b ])
                  | `Value v -> State.return [ assign target (R.Expr.bool ~loc:l v) ]
                in
                let* then_ = arm then_ in
                let+ else_ = arm else_ in
                [ R.Stmt.if_ ~loc:l a then_ else_ ])
          in
          let+ pending = after_branch ~loc:l before in
          (a_stmts @ stmts @ pending, v)
    | Some ((Eq | Neq) as op), _, [ a; b ]
      when is_physical path && not (exact_physical ctx.given.types a b) -> (
        let* b_stmts, b = expr ctx b in
        let* a_stmts, a = expr ctx a in
        let+ x = State.fresh "same" in
        let same = R.Expr.var ~loc:l (name ~loc:l x) in
        ( b_stmts @ a_stmts
          @ R.Stmt.local ~loc:l ~typ:(R.Type.bool ~loc:l) (ident ~loc:l x)
          @ [
              R.Stmt.havoc ~loc:l (name ~loc:l x);
              R.Stmt.assume ~loc:l
                (R.Spec.make
                   (R.Expr.binary ~loc:l Impl same (R.Expr.binary ~loc:l Eq a b)));
            ],
          match op with Eq -> same | _ -> R.Expr.not_ ~loc:l same ))
    | Some op, _, [ a; b ] ->
        let divisor = b.exp_loc in
        let* b_stmts, b = expr ctx b in
        let* a_stmts, a = expr ctx a in
        let stmts = b_stmts @ a_stmts in
        let nonzero () =
          State.check ~at:divisor "This divisor may be zero"
            (R.Expr.binary ~loc:(loc divisor) Neq b (R.Expr.int ~loc:(loc divisor) 0))
        in
        let checked what v =
          let+ overflow = State.no_overflow ~at what v in
          (stmts @ [ overflow ], v)
        in
        begin match op with
        | Plus -> checked "addition" (R.Expr.binary ~loc:l op a b)
        | Minus -> checked "subtraction" (R.Expr.binary ~loc:l op a b)
        | Mult -> checked "multiplication" (R.Expr.binary ~loc:l op a b)
        | Div ->
            let v = prelude_call ~loc:l Prelude.div [ a; b ] in
            let* nonzero = nonzero () in
            let+ overflow = State.no_overflow ~at "division" v in
            (stmts @ [ nonzero; overflow ], v)
        | Mod ->
            let+ nonzero = nonzero () in
            (stmts @ [ nonzero ], prelude_call ~loc:l Prelude.mod_ [ a; b ])
        | _ -> State.return (stmts, R.Expr.binary ~loc:l op a b)
        end
    | _, Some op, [ a ] -> (
        let* stmts, a = expr ctx a in
        match op with
        | `Not -> State.return (stmts, R.Expr.not_ ~loc:l a)
        | `Neg ->
            let v = R.Expr.neg ~loc:l a in
            let+ overflow = State.no_overflow ~at "negation" v in
            (stmts @ [ overflow ], v))
    | None, None, _ -> (
        let* path = State.of_result (Source.normalize_value_path e.exp_env ~at path) in
        (* A function copied per witness constructor is called as the copy for the
           constructor passed. *)
        let* path, declaration =
          match
            List.find ctx.given.specialized_calls ~f:(fun (paths, _, _) ->
                List.mem paths path ~equal:Path.same)
          with
          | None -> State.return (path, declaration)
          | Some (_, position, copies) -> (
              let copy =
                match Option.map (List.nth args position) ~f:(fun a -> a.exp_desc) with
                | Some (Texp_construct (_, cstr, [])) ->
                    List.find copies ~f:(fun (c, _, _) -> String.equal c cstr.cstr_name)
                | _ -> None
              in
              match copy with
              | Some (_, id, scheme) ->
                  State.return (Path.Pident id, { declaration with val_type = scheme })
              | None ->
                  State.of_result
                    (unsupported at
                       "A call of a function whose calls wait to be helped, with a \
                        witness other than a constructor"))
        in
        match resolved_call ctx.given.functions ctx.given.libraries path with
        | Some f when List.mem ctx.given.raising_library_calls f ~equal:String.equal ->
            State.of_result (unsupported at "A call of a library function that may raise")
        | Some f ->
            let* actual_target, type_instance =
              State.polymorphic_application ~values:args ctx ~at ~path
                ~declaration:declaration.val_type ~occurrence ~target:f
            in
            call ~actual_target ?type_instance ctx e f args
        | None -> (
            match path with
            | Pident _ -> State.of_result (unsupported at "A call of a local function")
            | _ -> State.of_result (unsupported at ("A call of " ^ Path.name path))))
    | _ -> State.of_result (unsupported at "This application")

(** The call of the top-level function [f] with [args], in [e]: a statement, whose result
    is kept in a variable unless it is unit. *)
and call ?actual_target ?type_instance ctx (e : Typedtree.expression) f
    (ocaml_args : Typedtree.expression list) =
  let* arguments, args = operands ctx ocaml_args in
  let* signature =
    match List.Assoc.find ctx.given.procedure_signatures f ~equal:String.equal with
    | None -> State.return None
    | Some signature ->
        begin match type_instance with
        | None -> State.return (Some signature)
        | Some _ when List.is_empty signature.procedure_parameters ->
            State.return (Some signature)
        | Some (_, arguments) ->
            begin match
              Datatypes.substitution signature.procedure_parameters arguments
            with
            | None ->
                State.of_result
                  (unsupported e.exp_loc "This generic ghost-call signature")
            | Some substitute ->
                State.return (Some (map_procedure_types signature ~f:substitute))
            end
        end
  in
  let inputs = Option.value_map signature ~default:[] ~f:(fun s -> s.procedure_inputs) in
  let outputs =
    Option.value_map signature ~default:[] ~f:(fun s -> s.procedure_outputs)
  in
  let returns_value =
    Option.value_map signature
      ~default:(not (is_unit e.exp_type))
      ~f:(fun signature -> signature.procedure_returns_value)
  in
  let run explicit =
    call_prepared ?actual_target ctx e f ocaml_args args ~explicit ~returns_value
      ~signature_outputs:outputs
  in
  let annotation =
    List.Assoc.find ctx.given.access_proofs
      (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum)
      ~equal:Poly.equal
  in
  match annotation with
  | None ->
      let+ statements, value, _ = run None in
      (arguments @ statements, value)
  | Some annotation ->
      let+ statements, value =
        access_proof ctx annotation ~result_type:e.exp_type
          ~input_types:(List.map inputs ~f:snd) ~output_types:(List.map outputs ~f:snd)
          (fun values -> run (Some values))
      in
      (arguments @ statements, value)

and call_prepared ?actual_target ctx (e : Typedtree.expression) f ocaml_args args
    ~explicit ~returns_value ~signature_outputs =
  let l = loc e.exp_loc in
  let stmts = [] in
  (* A lifted local function takes the parameters of the function it continues first. *)
  let prefix, captured, role =
    Option.value
      (List.Assoc.find ctx.given.lifted f ~equal:String.equal)
      ~default:(0, [], None)
  in
  let* (s : State.state) = State.get in
  let* prefix =
    State.of_result
      (if List.length s.carried.formals >= prefix then
         Ok (List.take s.carried.formals prefix)
       else error e.exp_loc "This call needs the parameters of the function it continues")
  in
  let* captured =
    State.of_result (captured_arguments ~at:e.exp_loc ~values:[] s.names captured)
  in
  let prefix = prefix @ captured in
  (* A ghost argument is the value of which the argument a precondition relates it to is a
     field, as [q] for [tail] in [fix_tail tail new_tail] after [push { tail; _ }]. *)
  let* ghosts =
    match explicit with
    | Some values -> State.return values
    | None ->
        State.of_result
          (all
             (Option.value
                (List.Assoc.find ctx.given.ghost_args f ~equal:String.equal)
                ~default:[])
             ~f:(fun equation ->
               let known =
                 Option.bind equation ~f:(fun (i, field) ->
                     match List.nth ocaml_args (i - List.length prefix) with
                     | Some { exp_desc = Texp_ident (Pident id, _, _); _ } ->
                         Option.bind (State.name_in s.names id) ~f:(fun x ->
                             List.find_map s.carried.fields_of ~f:(fun (y, (g, value)) ->
                                 Option.some_if
                                   (String.equal x y && String.equal g field)
                                   value))
                     (* The field itself of a variable, as [t.head]. *)
                     | Some
                         {
                           exp_desc =
                             Texp_field
                               ({ exp_desc = Texp_ident (Pident y, _, _); _ }, _, label);
                           _;
                         }
                       when String.equal label.lbl_name field ->
                         Option.map (State.name_in s.names y) ~f:(fun y ->
                             R.Expr.var ~loc:l (name ~loc:l y))
                     | _ -> None)
               in
               match (known, equation) with
               | Some value, _ -> Ok value
               | None, None ->
                   error e.exp_loc
                     "Caravan cannot tell the ghost argument of this call: give the \
                      callee a precondition that makes a parameter a field of it, as \
                      tail = q.tail"
               | None, Some (_, field) ->
                   error e.exp_loc
                     (Printf.sprintf
                        "Caravan cannot tell the ghost argument of this call: the \
                         argument is not a variable known to be the field %s of a value, \
                         as one a record pattern binds"
                        field)))
  in
  let args = prefix @ args @ ghosts in
  (* A recursive call before the function linearizes is a retry, which linearizes it in
     its place, with the atomic update's values of the implicit parameters, as does a call
     of a function that continues the update, or of another atomic function. *)
  let* au_state = au_state in
  let* retry =
    match ctx.au with
    | Some au
      when String.equal au.self (Option.value actual_target ~default:f)
           || Option.exists role ~f:(fun r -> Ident.same r au.role) ->
        let+ opened = open_for_call au ~at:e.exp_loc in
        Option.map opened ~f:(fun (opening, values) -> (au, opening, values))
    (* A call of another atomic function before this one linearizes delegates its update
       to it, as Saturn's [let pop_opt t = pop_as t Backoff.default Option]. *)
    | Some au
      when List.mem ctx.given.atomic_procedures f ~equal:String.equal
           && Poly.equal au_state (Some Pending) ->
        let+ opened = open_for_call au ~at:e.exp_loc in
        Option.map opened ~f:(fun (opening, values) -> (au, opening, values))
    | _ -> State.return None
  in
  let opening, implicit =
    Option.value_map retry ~default:([], []) ~f:(fun (_, o, values) -> (o, values))
  in
  (* The retry commits with its result. *)
  let closing value outcome =
    Option.value_map retry ~default:(State.return []) ~f:(fun (au, _, _) ->
        au.close Commit_call ~value
          ~outcome:(Option.value_map outcome ~default:Returned ~f:(fun o -> Outcome o)))
  in
  (* The latest snapshot witnesses the facts about earlier states that the callee
     requires, with the arguments' positions in it. *)
  let* path = get_path in
  let* env = scope_env ctx in
  let argument_type index =
    Option.map
      (List.nth ocaml_args (index - List.length prefix))
      ~f:(fun (argument : Typedtree.expression) -> argument.exp_type)
  in
  let* witnesses =
    State.all
      (Option.value (List.Assoc.find ctx.given.pasts f ~equal:String.equal) ~default:[])
      ~f:(fun (inv, field, i) ->
        let* st =
          resolve_shared_structure ?element_type:(argument_type i) env ~at:e.exp_loc
            ~invariant:inv ~field
        in
        let inv = st.invariant in
        let* argument =
          State.of_result
            (Report.expect ~at:e.exp_loc "The argument a past fact is about"
               (List.nth args i))
        in
        match
          ( List.Assoc.find path.snapshots inv ~equal:String.equal,
            known_position path.positions inv field argument )
        with
        | _, Some p -> State.return [ p.pos_snapshot; p.pos_k ]
        | Some (latest :: _), None ->
            let+ index =
              State.of_result
                (Report.expect ~at:e.exp_loc
                   ("The snapshot index of field " ^ field)
                   (List.Assoc.find latest.indices field ~equal:String.equal))
            in
            [
              state_of ~loc:l st (grown st latest.values);
              R.Expr.index ~loc:l index argument;
            ]
        | _ ->
            State.of_result
              (error e.exp_loc
                 "This call needs a fact about an earlier state, of which no snapshot \
                  was taken"))
  in
  (* A library's procedure is qualified by its module, as [Backoff.once]. *)
  let callee_name = qualified_name ~loc:l (Option.value actual_target ~default:f) in
  let callee = R.Expr.call ~loc:l callee_name (args @ List.concat witnesses @ implicit) in
  (* The ghost results witnessing facts about the state after the call: the caller's own,
     if the callee continues its update with the same ones. *)
  let* ghost_facts =
    let metadata =
      Option.value
        (List.Assoc.find ctx.given.past_returns f ~equal:String.equal)
        ~default:[]
    in
    State.all metadata ~f:(fun past ->
        let parameters = past.past_inputs @ [ past.past_result; past.past_element ] in
        let* worker =
          State.of_result
            (Generic_parameters.discover ~expand:(Datatypes.expand env.data)
               ~key:past.past_invariant ~name:past.past_invariant ~at:e.exp_loc
               ~explicit:(List.length past.past_inputs)
               parameters)
        in
        let* element_type =
          if List.is_empty worker.variables then State.return past.past_element
          else
            let* () =
              if
                List.length past.past_inputs = List.length prefix + List.length ocaml_args
              then State.return ()
              else
                State.of_result
                  (unsupported e.exp_loc "This lifted history call's type arguments")
            in
            let* arguments =
              State.of_result
                (Generic_parameters.instantiate ~environment:env.ctx.given.env
                   ~expand:(Datatypes.expand env.data) ~at:e.exp_loc worker
                   (List.init (List.length prefix) ~f:(fun _ -> None)
                   @ List.map ocaml_args ~f:(fun (argument : Typedtree.expression) ->
                       Some argument.exp_type)
                   @ [ Some e.exp_type; None ]))
            in
            State.return
              (List.last_exn (Generic_parameters.parameter_types worker arguments))
        in
        let+ st =
          resolve_shared_structure ~element_type env ~at:e.exp_loc
            ~invariant:past.past_invariant ~field:past.past_field
        in
        { past with past_invariant = st.invariant; past_element = element_type })
  in
  let ghost_count = 2 * List.length ghost_facts in
  let* ghost_decls, ghosts =
    match retry with
    | Some (au, _, _) when ghost_count > 0 && List.length au.ghost_results = ghost_count
      ->
        State.return ([], au.ghost_results)
    | _ ->
        let+ fresh =
          State.all ghost_facts ~f:(fun past ->
              let st =
                List.find_exn ctx.given.shared.structures ~f:(fun st ->
                    String.equal st.invariant past.past_invariant)
              in
              let* position = State.fresh "position" in
              let+ snapshot = State.fresh "snapshot" in
              [
                ( snapshot,
                  R.Type.named ~loc:l
                    (generated_module_member ~loc:l (module_name st "state") "T")
                    [] );
                (position, R.Type.int ~loc:l);
              ])
        in
        let fresh = List.concat fresh in
        ( List.concat_map fresh ~f:(fun (x, typ) ->
              R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x)),
          List.map fresh ~f:(fun (x, _) -> R.Expr.var ~loc:l (name ~loc:l x)) )
  in
  (* The ghost results witness the positions of the entries the callee ensures. *)
  let rec witnessed facts ghosts =
    match (facts, ghosts) with
    | past :: facts, snapshot :: k :: ghosts ->
        let rest = witnessed facts ghosts in
        begin match past.past_entry args with
        | Some e ->
            {
              pos_inv = past.past_invariant;
              pos_field = past.past_field;
              pos_element = e;
              pos_snapshot = snapshot;
              pos_k = k;
            }
            :: rest
        | None -> rest
        end
    | _ -> []
  in
  let* () =
    modify_path (fun path ->
        { path with positions = witnessed ghost_facts ghosts @ path.positions })
  in
  let* public =
    State.all signature_outputs ~f:(fun (_, ty) ->
        let* raven = State.fresh "ghost_result" in
        let+ raven_type = State.typ ctx ~at:e.exp_loc ty in
        ( R.Expr.var ~loc:l (name ~loc:l raven),
          R.Stmt.local ~loc:l ~ghost:true ~typ:raven_type (ident ~loc:l raven) ))
  in
  let public_values = List.map public ~f:fst in
  (* A callee that may raise returns its outcome last, which the caller propagates. *)
  (* A call with a witness constructor raises what the callee does for it. *)
  let witness_set =
    Option.bind (List.Assoc.find ctx.given.witness_raising f ~equal:String.equal)
      ~f:(fun (position, sets) ->
        match Option.map (List.nth ocaml_args position) ~f:(fun a -> a.exp_desc) with
        | Some (Texp_construct (_, cstr, [])) ->
            List.Assoc.find sets cstr.cstr_name ~equal:String.equal
        | _ -> None)
  in
  let* outcome =
    match
      Option.map (List.Assoc.find ctx.given.raising f ~equal:String.equal) ~f:(fun set ->
          Option.value witness_set ~default:set)
    with
    | None -> State.return None
    | Some (State.Raises []) ->
        (* The callee returns its outcome, which is none for this witness. *)
        let* typ = State.typ ctx ~at:e.exp_loc outcome_type in
        let+ x = State.fresh "raised" in
        let v = R.Expr.var ~loc:l (name ~loc:l x) in
        Some
          ( R.Stmt.local ~loc:l ~typ (ident ~loc:l x),
            v,
            [
              R.Stmt.assert_ ~loc:l
                (R.Spec.make (R.Expr.binary ~loc:l Eq v (no_exception ~loc:l typ)));
            ] )
    | Some set ->
        let* handlers = State.gets (fun (s : State.state) -> s.carried.handlers) in
        (* Leaving the function must commit its atomic update: only a retry does. *)
        let* () =
          match (ctx.au, retry, handlers) with
          | Some _, None, [] ->
              State.of_result
                (unsupported e.exp_loc
                   "A call that may raise, other than a retry, in a function with an \
                    atomic contract")
          | _ -> State.return ()
        in
        let* typ = State.typ ctx ~at:e.exp_loc outcome_type in
        let* x = State.fresh "raised" in
        let v = R.Expr.var ~loc:l (name ~loc:l x) in
        let+ leave = propagate ~at:e.exp_loc ~certain:false ~typ v set in
        Some (R.Stmt.local ~loc:l ~typ (ident ~loc:l x), v, leave)
  in
  let ghost_decls =
    List.concat_map public ~f:snd @ ghost_decls
    @ Option.value_map outcome ~default:[] ~f:(fun (decl, _, _) -> decl)
  in
  let ghosts =
    public_values @ ghosts @ Option.to_list (Option.map outcome ~f:(fun (_, v, _) -> v))
  in
  let propagation =
    Option.value_map outcome ~default:[] ~f:(fun (_, _, leave) -> leave)
  in
  let outcome_value = Option.map outcome ~f:(fun (_, v, _) -> v) in
  if is_unit e.exp_type && not returns_value then
    let+ closing = closing (unit_value ~loc:l) outcome_value in
    let call =
      match ghosts with
      | [] -> [ R.Stmt.call ~loc:l callee ]
      | _ -> ghost_decls @ [ R.Stmt.assign ~loc:l ghosts (R.Stmt.expr_rhs callee) ]
    in
    (stmts @ opening @ call @ closing @ propagation, unit_value ~loc:l, public_values)
  else
    let* typ = State.typ ctx ~at:e.exp_loc e.exp_type in
    let* x = State.fresh "tmp" in
    let v = R.Expr.var ~loc:l (name ~loc:l x) in
    let def =
      match ghosts with
      | [] -> R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs callee) (ident ~loc:l x)
      | _ ->
          R.Stmt.local ~loc:l ~typ (ident ~loc:l x)
          @ ghost_decls
          @ [ R.Stmt.assign ~loc:l (v :: ghosts) (R.Stmt.expr_rhs callee) ]
    in
    let* closing = closing v outcome_value in
    (* A retry that raised committed the update with its result, which the function
       returns. *)
    let+ (carried : State.carried) = State.gets (fun (s : State.state) -> s.carried) in
    let returned =
      match (retry, outcome_value, carried.exit) with
      | Some (au, _, _), Some _, Some { results = result :: _; _ } when au.has_result ->
          [ R.Stmt.assign ~loc:l [ result ] (R.Stmt.expr_rhs v) ]
      | _ -> []
    in
    (stmts @ opening @ def @ closing @ returned @ propagation, v, public_values)

(** The constructor argument [arg], with value [value], named and checked admissible if it
    is a nested constructor application. A literal's admissibility is then established one
    constructor at a time, as the solver unfolds a recursive predicate only to a bounded
    depth. *)
and established ctx (arg : Typedtree.expression) value =
  let l = loc arg.exp_loc in
  match arg.exp_desc with
  | Texp_construct (_, _, _ :: _)
    when Option.is_some (Datatypes.admissible ~loc:l ctx.given.types arg.exp_type value)
    ->
      let* typ = State.typ ctx ~at:arg.exp_loc arg.exp_type in
      let* () = State.note_domain ctx.given.types arg.exp_type in
      let+ x = State.fresh "tmp" in
      ( R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs value) (ident ~loc:l x)
        @ assert_admissible ctx ~loc:l arg.exp_type x,
        R.Expr.var ~loc:l (name ~loc:l x) )
  | _ -> State.return ([], value)

(** The statements evaluating [args], right to left as OCaml does, and their values. *)
and operands ctx (args : Typedtree.expression list) =
  let+ evaluated = State.all (List.rev args) ~f:(fun arg -> expr ctx arg) in
  (List.concat_map evaluated ~f:fst, List.rev_map evaluated ~f:snd)

(** The accesses and condition for matching [p] against [v], and its bindings. *)
and pattern ?guard ctx (p : Typedtree.pattern) (v : R.Expr.t) =
  let at = p.pat_loc in
  let l = loc at in
  let conjoin conds =
    List.reduce (List.filter_opt conds) ~f:(fun a b -> R.Expr.binary ~loc:l And a b)
  in
  let components guard ps values =
    let+ matched =
      State.all (List.zip_exn ps values) ~f:(fun (p, (access, v)) ->
          let+ nested, cond, binds = pattern ?guard ctx p v in
          (access @ nested, cond, binds))
    in
    ( List.concat_map matched ~f:(fun (access, _, _) -> access),
      conjoin (List.map matched ~f:(fun (_, cond, _) -> cond)),
      List.concat_map matched ~f:(fun (_, _, binds) -> binds) )
  in
  match p.pat_desc with
  | Tpat_any -> State.return ([], None, [])
  | Tpat_var (id, _, _) -> State.return ([], None, [ (id, v, p.pat_type) ])
  | Tpat_alias (q, id, _, _, _) ->
      let+ access, cond, binds = pattern ?guard ctx q v in
      (access, cond, binds @ [ (id, v, p.pat_type) ])
  | Tpat_constant (Const_int n) ->
      State.return ([], Some (R.Expr.binary ~loc:l Eq v (R.Expr.int ~loc:l n)), [])
  | Tpat_tuple ps ->
      let values = List.mapi ps ~f:(fun i _ -> ([], R.Expr.tuple_get ~loc:l v i)) in
      components guard (List.map ps ~f:snd) values
  | Tpat_record (fields, _) ->
      let* parts =
        State.all fields ~f:(fun (_, label, p) ->
            let* field = State.field_of_label ctx.given ~at label in
            match field with
            | Some (field, false) ->
                State.return (p, ([], R.Expr.field ~loc:l v (qualified_name ~loc:l field)))
            | Some (field, true) ->
                let+ access, value =
                  State.ordinary_read ?guard ctx.given ~at ~field ~elt:label.lbl_arg v
                in
                (p, (access, value))
            | None -> State.of_result (unsupported at "This field"))
      in
      components guard (List.map parts ~f:fst) (List.map parts ~f:snd)
  | Tpat_construct (_, { cstr_name = ("true" | "false") as b; _ }, [], _) ->
      State.return
        ( [],
          Some (R.Expr.binary ~loc:l Eq v (R.Expr.bool ~loc:l (String.equal b "true"))),
          [] )
  | Tpat_construct (_, { cstr_name = "()"; _ }, [], _) -> State.return ([], None, [])
  | Tpat_construct (_, cstr, ps, _) ->
      begin match occurrence_constructor ctx.given.types p.pat_type cstr with
      | None -> State.of_result (unsupported at "This constructor")
      | Some (_, c) ->
          let is_c, fields =
            match shared_exception ctx c with
            (* The application's own exception, in a functor body it shares. *)
            | Some app ->
                ( shared_exception_call ~loc:l app "is" c [ v ],
                  List.mapi c.fields ~f:(fun i _ ->
                      ( [],
                        shared_exception_call ~loc:l app
                          ("field$" ^ Int.to_string i)
                          c [ v ] )) )
            | None ->
                ( R.Expr.is_ ~loc:l v (ident ~loc:l c.raven),
                  List.map c.fields ~f:(fun f ->
                      ([], R.Expr.field ~loc:l v (qualified_name ~loc:l f))) )
          in
          let+ access, cond, binds =
            components (conjoin [ guard; Some is_c ]) ps fields
          in
          (access, conjoin [ Some is_c; cond ], binds)
      end
  | Tpat_or (p1, p2, _) -> begin
      let* a1, c1, b1 = pattern ?guard ctx p1 v in
      let* a2, c2, b2 = pattern ?guard ctx p2 v in
      match (a1, a2, c1, c2, b1, b2) with
      | [], [], Some c1, Some c2, [], [] ->
          State.return ([], Some (R.Expr.binary ~loc:l Or c1 c2), [])
      | [], [], _, _, [], [] -> State.return ([], None, [])
      | _ :: _, _, _, _, _, _ | _, _ :: _, _, _, _, _ ->
          State.of_result (unsupported at "An or-pattern reading a mutable field")
      | _ -> State.of_result (unsupported at "An or-pattern binding variables")
    end
  | _ -> State.of_result (unsupported at "This pattern")

(** The cases of a match on the value [v], with the value of the matching one assigned to
    [target] if there is one; [total] if OCaml found them exhaustive. *)
and match_cases ?commits ?otherwise ?arm ~tail ctx ~at v
    (cases : (Typedtree.pattern * Typedtree.expression) list) ~total target =
  let l = loc at in
  let* before = pending_count in
  let* enclosing_names = State.get_scope in
  (* Each case starts in the state of the atomic update before the match. *)
  let* start = get_path in
  let commits =
    match commits with
    | Some commits -> commits
    | None -> List.map cases ~f:(fun _ -> None)
  in
  (* Whether each case linearizes the function, if the scrutinee is the value of a read
     that left the atomic update open, by the case's body. *)
  let case_commits = List.zip_exn (List.map cases ~f:snd) commits in
  (* The body of a case, after defining the variables of its pattern, with the join of
     the positions after it, and the path it ends in. *)
  let case_body ?(names = enclosing_names) join binds (rhs : Typedtree.expression) =
    let* () = State.set_scope names in
    let+ (stmts, join), ended =
      State.arm start
        (let commits =
           Option.join
             (List.Assoc.find case_commits rhs ~equal:(fun a b ->
                  Poly.equal a.exp_loc b.exp_loc))
         in
         let* entry = enter_arm ctx ~commits in
         let* defs =
           State.all binds ~f:(fun (id, value, t) ->
               let* typ = State.typ ctx ~at t in
               let* () = State.note_domain ctx.given.types t in
               let+ x = State.bind_name ~typ:t id in
               R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs value) (ident ~loc:l x)
               @ assert_admissible ctx ~loc:l t x)
         in
         (* A case of a match on a witness has its own types, and its value is converted
            to the type the witness selects. *)
         let rhs_ctx, conversion =
           match arm with
           | None -> (ctx, None)
           | Some arm ->
               let types, conversion = arm rhs in
               ({ ctx with given = { ctx.given with types } }, conversion)
         in
         let* stmts, value = expr ~tail rhs_ctx rhs in
         let value =
           Option.value_map conversion ~default:value ~f:(fun conversion ->
               R.Expr.call ~loc:l
                 (Qualified_name.raven ~loc:l (Qualified_name.of_string conversion))
                 [ value ])
         in
         let* finish = finish_arm ctx ~tail value in
         let assignment =
           Option.value_map target ~default:[] ~f:(fun t -> [ assign t value ])
         in
         let* assigned, join = end_arm ctx join ~start:start.positions in
         let+ stmts =
           nest (entry @ List.concat defs @ stmts @ finish @ assignment @ assigned)
         in
         (stmts, join))
    in
    (stmts, join, ended)
  in
  (* No case matching is a failure, or what [otherwise] does. *)
  let not_exhaustive () =
    match otherwise with
    | Some otherwise -> State.return otherwise
    | None ->
        let+ check =
          State.check ~at "This match may not be exhaustive" (R.Expr.bool ~loc:l false)
        in
        [ check ]
  in
  let* flat = flat_cases ctx v cases in
  let* stmts, join, ends =
    match flat with
    | Some flat ->
        let* join, raven_cases, ends =
          State.fold flat ~init:(empty_join, [], [])
            ~f:(fun (join, raven_cases, ends) (case, binds, in_range, rhs, names) ->
              let+ body, join, ended = case_body ~names join binds rhs in
              (join, (case, in_range @ body) :: raven_cases, ended :: ends))
        in
        let has_default =
          List.exists flat ~f:(fun (case, _, _, _, _) ->
              match case with R.Expr.Default -> true | Case _ -> false)
        in
        let+ default =
          if total || has_default then State.return []
          else
            let+ fails = not_exhaustive () in
            [ (R.Expr.Default, fails) ]
        in
        let cases = List.rev raven_cases @ default in
        let statements =
          match cases with
          | [ (R.Expr.Default, body) ] -> body
          | _ -> [ R.Stmt.match_ ~loc:l v cases ]
        in
        (statements, join, ends)
    | None ->
        let rec chain join ends = function
          | [] ->
              let+ fails = if total then State.return [] else not_exhaustive () in
              (fails, join, ends)
          | [ (p, rhs) ] when total ->
              let* access, _, binds = pattern ctx p v in
              let+ body, join, ended = case_body join binds rhs in
              (access @ body, join, ended :: ends)
          | (p, rhs) :: rest -> begin
              let* access, cond, binds = pattern ctx p v in
              let* body, join, ended = case_body join binds rhs in
              let ends = ended :: ends in
              match cond with
              | None -> State.return (access @ body, join, ends)
              | Some cond ->
                  let+ rest, join, ends = chain join ends rest in
                  (access @ [ R.Stmt.if_ ~loc:l cond body rest ], join, ends)
            end
        in
        chain empty_join [] cases
  in
  let state (path : State.path) = Option.map path.au ~f:(fun au -> au.au_state) in
  let* () =
    set_au_state
      (Option.first_some
         (List.reduce (List.filter_map ends ~f:state) ~f:join_au)
         (state start))
  in
  let* () =
    modify_path (fun path ->
        {
          path with
          snapshots = common_snapshots (List.map ends ~f:(fun ended -> ended.snapshots));
          positions =
            join_positions join ~start:start.positions
              (List.map ends ~f:(fun ended -> ended.positions));
        })
  in
  let+ pending = after_branch ~loc:l before in
  join.decls @ stmts @ pending

(** The cases of a Raven match on [v] for [cases], if their patterns are flat: distinct
    constructors with variables or [_] as arguments, possibly followed by a variable or
    [_] matching anything else. *)
and flat_cases ctx v cases =
  let* enclosing_names = State.get_scope in
  let flat_arg (p : Typedtree.pattern) =
    match p.pat_desc with
    | Tpat_any -> Some None
    | Tpat_var (id, _, _) -> Some (Some (id, p.pat_type))
    | _ -> None
  in
  let rec flat seen = function
    | [] -> Some []
    | [ ((p : Typedtree.pattern), rhs) ] when Option.is_some (flat_arg p) ->
        Some [ (`Any (Option.map (Option.join (flat_arg p)) ~f:fst, p), rhs) ]
    | ((p : Typedtree.pattern), rhs) :: rest ->
        begin match p.pat_desc with
        | Tpat_construct (_, cstr, ps, _) ->
            begin match
              ( occurrence_constructor ctx.given.types p.pat_type cstr,
                Option.all (List.map ps ~f:flat_arg) )
            with
            (* A shared functor body's exception is matched through its module. *)
            | Some (_, c), Some args
              when (not (List.mem seen c.raven ~equal:String.equal))
                   && Option.is_none (shared_exception ctx c) ->
                Option.map
                  (flat (c.raven :: seen) rest)
                  ~f:(fun rest -> (`Ctor (c, args, p), rhs) :: rest)
            | _ -> None
            end
        | _ -> None
        end
  in
  let case item =
    let* () = State.set_scope enclosing_names in
    match item with
    | `Any (id, (p : Typedtree.pattern)), rhs ->
        let binds =
          Option.value_map id ~default:[] ~f:(fun id -> [ (id, v, p.pat_type) ])
        in
        let+ scope = State.get_scope in
        (R.Expr.Default, binds, [], rhs, scope)
    | `Ctor ((c : Datatypes.ctor), args, (p : Typedtree.pattern)), rhs ->
        let l = loc p.pat_loc in
        let var = function
          | None -> State.return (ident ~loc:l "_", [])
          | Some (id, t) ->
              let* () = State.note_domain ctx.given.types t in
              let+ x = State.bind_name ~typ:t id in
              (ident ~loc:l x, assert_admissible ctx ~loc:l t x)
        in
        let* vars = State.all args ~f:var in
        let+ scope = State.get_scope in
        ( R.Expr.Case (ident ~loc:l c.raven, List.map vars ~f:fst),
          [],
          List.concat_map vars ~f:snd,
          rhs,
          scope )
  in
  let* result =
    match flat [] cases with
    | Some items ->
        let+ cases = State.all items ~f:case in
        Some cases
    | None -> State.return None
  in
  let+ () = State.set_scope enclosing_names in
  result

(** [if c then e1 else e2], with its value assigned to [target] if there is one. *)
and conditional_arms ctx ~at ?polarity ~tail c (e1 : Typedtree.expression)
    (e2 : Typedtree.expression option) target =
  let l = loc at in
  (* Each arm starts in the state of the atomic update before the branch; if [c] is the
     result of the [compare_and_set] that left the update open, the arms close it. *)
  let* start = get_path in
  let arm join taken e =
    State.arm start
      (let* entry =
         enter_arm ctx ~commits:(Option.map polarity ~f:(fun p -> Bool.equal p taken))
       in
       let* stmts =
         match e with
         | None -> finish_arm ctx ~tail (unit_value ~loc:l)
         | Some e ->
             let* stmts, v = expr ~tail ctx e in
             let+ finish = finish_arm ctx ~tail v in
             let assignment =
               Option.value_map target ~default:[] ~f:(fun t -> [ assign t v ])
             in
             stmts @ finish @ assignment
       in
       let* assigned, join = end_arm ctx join ~start:start.positions in
       let+ stmts = nest (entry @ stmts @ assigned) in
       (stmts, join))
  in
  let* (then_, join), then_end = arm empty_join true (Some e1) in
  let* (else_, join), else_end = arm join false e2 in
  let state (path : State.path) = Option.map path.au ~f:(fun au -> au.au_state) in
  let* () = set_au_state (Option.map2 (state then_end) (state else_end) ~f:join_au) in
  let+ () =
    modify_path (fun path ->
        {
          path with
          snapshots = common_snapshots [ then_end.snapshots; else_end.snapshots ];
          positions =
            join_positions join ~start:start.positions
              [ then_end.positions; else_end.positions ];
        })
  in
  join.decls @ [ R.Stmt.if_ ~loc:l c then_ else_ ]

(** [if c then e1 else e2], with a pending point after it if an arm has one. *)
and conditional ctx ~at ?polarity ~tail c e1 e2 target =
  let* before = pending_count in
  let* stmts = conditional_arms ctx ~at ?polarity ~tail c e1 e2 target in
  let+ pending = after_branch ~loc:(loc at) before in
  stmts @ pending

(** For a loop at [at] whose [body] may raise: its outcome variable's declaration, the
    variable and its type, the condition that nothing was raised, which continues the loop
    and guards the invariants of [spec], and what holds when it has: the loop's [raises]
    clauses, or if it has none and no handler of the function covers it, the function's,
    proven where it raises. *)
and loop_raising ctx ~at ~(spec : S.loop_spec) (cond : Typedtree.expression option) body =
  let l = loc at in
  let raises (e : Typedtree.expression) =
    Exceptions.raised
      ~callee:(fun path _ ->
        Option.value_map (resolved_call ctx.given.functions ctx.given.libraries path)
          ~default:(State.Raises []) ~f:(fun f ->
            Option.value
              (List.Assoc.find ctx.given.raising f ~equal:String.equal)
              ~default:(State.Raises [])))
      (Exceptions.uses ~key:(Exceptions.key ctx.given.types) e)
  in
  let raising e = match raises e with State.Raises [] -> false | _ -> true in
  match cond with
  | Some cond when raising cond ->
      State.of_result (unsupported cond.exp_loc "A loop condition that may raise")
  | _ when not (raising body) -> State.return None
  | _ ->
      let* typ = State.typ ctx ~at outcome_type in
      let* k = State.fresh "raised" in
      let outcome = R.Expr.var ~loc:l (name ~loc:l k) in
      let none = no_exception ~loc:l typ in
      let* (carried : State.carried) = State.gets (fun (s : State.state) -> s.carried) in
      let unraised = R.Expr.binary ~loc:l Eq outcome none in
      let terms =
        match (spec.loop_raises, carried.handlers, carried.exit) with
        | _ :: _, _, _ ->
            Exceptions.raises_postconditions ctx.given.types ~at spec.loop_raises
              (raises body)
        | [], [], Some exit -> exit.raises_terms
        | [], _, _ -> []
      in
      let+ exceptional =
        match terms with
        | _ :: _ ->
            let* env = scope_env ctx in
            let env =
              {
                (bind env outcome_name (Raven k)) with
                var_types = (outcome_name, outcome_type) :: env.var_types;
              }
            in
            let+ terms = State.all terms ~f:(Spec_terms.formula env) in
            [
              R.Spec.make
                (R.Expr.binary ~loc:l Impl
                   (R.Expr.binary ~loc:l Neq outcome none)
                   (List.reduce_exn terms ~f:(R.Expr.binary ~loc:l And)));
            ]
        | [] -> State.return []
      in
      Some
        ( R.Stmt.local ~loc:l ~const:false ~typ ~init:(R.Stmt.expr_rhs none)
            (ident ~loc:l k),
          outcome,
          typ,
          unraised,
          exceptional )

(** The statements [translate ()] of a loop's body, as the protected part of a handler
    catching nothing if the loop may raise, as [raising] says, with what may reach it. *)
and in_loop raising translate =
  match raising with
  | None ->
      let+ stmts = translate () in
      (stmts, State.Raises [])
  | Some (_, outcome, outcome_type, _, _) ->
      let* (enclosing : State.carried) =
        State.gets (fun (s : State.state) -> s.carried)
      in
      let* () =
        State.modify_carried (fun c ->
            {
              c with
              handlers = { outcome; outcome_type; reaching = Raises [] } :: c.handlers;
            })
      in
      let* stmts = translate () in
      let* stmts = nest stmts in
      let* reaching =
        State.gets (fun (s : State.state) ->
            match s.carried.handlers with
            | handler :: _ -> handler.reaching
            | [] -> State.Raises [])
      in
      let+ () =
        State.modify_carried (fun c -> { c with handlers = enclosing.handlers })
      in
      (stmts, reaching)

(** The statements and value of [e], whose [protected] statements, computing its value
    into a target, may raise: if they do, the handler [cases] match the exception, and one
    no case catches propagates; if not, the [normal] statements follow. *)
and handled ctx ~at ~tail (e : Typedtree.expression) ~cases ~protected ~normal =
  let l = loc at in
  let* typ = State.typ ctx ~at outcome_type in
  let* k = State.fresh "raised" in
  let outcome = R.Expr.var ~loc:l (name ~loc:l k) in
  let* before = pending_count in
  let* stmts, v =
    branch ctx e (fun target ->
        (* The protected part, after which an exception may be pending. *)
        let* (enclosing : State.carried) =
          State.gets (fun (s : State.state) -> s.carried)
        in
        let* () =
          State.modify_carried (fun c ->
              {
                c with
                handlers =
                  { outcome; outcome_type = typ; reaching = Raises [] } :: c.handlers;
              })
        in
        let* stmts = protected target in
        let* protected = nest stmts in
        let* reaching =
          State.gets (fun (s : State.state) ->
              match s.carried.handlers with
              | handler :: _ -> handler.reaching
              | [] -> Raises [])
        in
        let* () =
          State.modify_carried (fun c ->
              {
                c with
                handlers = enclosing.handlers;
                caught =
                  List.concat_map cases ~f:(fun (p, _) ->
                      List.map (Typedtree.pat_bound_idents p) ~f:(fun id ->
                          (id, reaching)))
                  @ c.caught;
              })
        in
        (* The cases, on the exception raised; one no case catches propagates. *)
        let handled, catch_all =
          Exceptions.handled ~key:(Exceptions.key ctx.given.types) (List.map cases ~f:fst)
        in
        let* otherwise =
          match unhandled reaching ~handled ~catch_all with
          | Raises [] -> State.return []
          | set -> propagate ~at ~certain:true ~typ outcome set
        in
        let* handling =
          match_cases ~otherwise ~tail ctx ~at
            (R.Expr.field ~loc:l outcome (qualified_name ~loc:l "value"))
            cases ~total:catch_all target
        in
        let* () = State.modify_carried (fun c -> { c with caught = enclosing.caught }) in
        let+ normal = normal target in
        R.Stmt.local ~loc:l ~const:false ~typ
          ~init:(R.Stmt.expr_rhs (no_exception ~loc:l typ))
          (ident ~loc:l k)
        @ protected
        @ [
            R.Stmt.if_ ~loc:l
              (R.Expr.binary ~loc:l Neq outcome (no_exception ~loc:l typ))
              handling normal;
          ])
  in
  let+ pending = after_branch ~loc:l before in
  (stmts @ pending, v)

(** The statements [make target] computing the value of [e] into a new variable [target],
    and that variable; no variable if [e] is of type unit. *)
and branch ctx (e : Typedtree.expression) make =
  let l = loc e.exp_loc in
  if is_unit e.exp_type then
    let+ stmts = make None in
    (stmts, unit_value ~loc:l)
  else
    let* typ = State.typ ctx ~at:e.exp_loc e.exp_type in
    let* x = State.fresh "tmp" in
    let+ stmts = make (Some (x, l)) in
    ( R.Stmt.local ~loc:l ~const:false ~typ (ident ~loc:l x) @ stmts,
      R.Expr.var ~loc:l (name ~loc:l x) )

and assign (x, l) v =
  R.Stmt.assign ~loc:l [ R.Expr.var ~loc:l (name ~loc:l x) ] (R.Stmt.expr_rhs v)

(** The pure expression [e] as a Raven expression, with the values of its let-bound
    variables in [values]; [funcs] are the functions it may call, by their OCaml compiler
    paths, with their Raven names. *)
and pure ?(reads = []) ctx ~funcs (values : (string * R.Expr.t) list)
    (e : Typedtree.expression) : R.Expr.t State.t =
  let at = e.exp_loc in
  let l = loc at in
  let pure_in values = pure ~reads ctx ~funcs values in
  let not_pure what =
    State.of_result
      (unsupported at (what ^ " in a function that contracts use, which must be pure,"))
  in
  let* names = State.gets (fun (s : State.state) -> s.names) in
  match e.exp_desc with
  | Texp_unreachable -> raw_default ctx ~at e.exp_type
  | Texp_ident (Pident id, _, _) ->
      begin match
        ( List.Assoc.find values (Ident.unique_name id) ~equal:String.equal,
          State.name_in names id )
      with
      | Some v, _ -> State.return v
      | None, Some x -> State.return (R.Expr.var ~loc:l (name ~loc:l x))
      | None, None -> not_pure "A function used as a value"
      end
  | Texp_ident (p, _, _) ->
      begin match stdlib_name p with
      | Some "max_int" -> State.return (R.Expr.int ~loc:l Prelude.max_int)
      | Some "min_int" -> State.return (R.Expr.int ~loc:l Prelude.min_int)
      | _ -> not_pure "This identifier"
      end
  | Texp_constant (Const_int n) -> State.return (R.Expr.int ~loc:l n)
  | Texp_construct ({ txt = Lident (("true" | "false") as b); _ }, _, []) ->
      State.return (R.Expr.bool ~loc:l (String.equal b "true"))
  | Texp_construct ({ txt = Lident "()"; _ }, _, []) -> State.return (unit_value ~loc:l)
  | Texp_construct (_, cstr, args) ->
      begin match occurrence_constructor ctx.given.types e.exp_type cstr with
      | None -> not_pure "This constructor"
      | Some (d, c) ->
          let* args = State.all args ~f:(pure_in values) in
          constructor_value ctx ~at ~result_type:e.exp_type d c args
      end
  | Texp_record { fields; extended_expression = None; _ } ->
      begin match Datatypes.instantiated ctx.given.types e.exp_type with
      | Some ({ heap = None; ctors = [ constructor ]; _ } as data) ->
          let* arguments =
            State.all (Array.to_list fields) ~f:(fun (_, definition) ->
                match definition with
                | Typedtree.Overridden (_, expression) -> pure_in values expression
                | Kept _ -> not_pure "This record")
          in
          constructor_value ctx ~at ~result_type:e.exp_type data constructor arguments
      | Some _ | None -> not_pure "A mutable record allocation"
      end
  | Texp_tuple components ->
      let+ components = State.all components ~f:(fun (_, c) -> pure_in values c) in
      R.Expr.tuple ~loc:l components
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, _); _ },
        [ (Nolabel, Arg ({ exp_desc = Texp_ident (Pident r, _, _); _ } as cell)) ] )
    when Option.equal String.equal (stdlib_name path) (Some "!") ->
      begin match
        (State.name_in names r, Datatypes.desc ctx.given.types cell.exp_type)
      with
      | Some x, Tconstr (_, [ elt ], _) -> begin
          let* field = State.ref_field ctx.given ~at elt in
          match List.Assoc.find reads (x, field) ~equal:Poly.equal with
          | Some v -> State.return v
          | None -> not_pure "A read of a reference"
        end
      | _ -> not_pure "A read of a reference"
      end
  | Texp_field ({ exp_desc = Texp_ident (Pident r, _, _); _ }, _, label)
    when Option.is_some (State.name_in names r) -> begin
      let* field = State.field_of_label ctx.given ~at label in
      let x = Option.value_exn (State.name_in names r) in
      match field with
      | Some (field, true) ->
          begin match List.Assoc.find reads (x, field) ~equal:Poly.equal with
          | Some v -> State.return v
          | None -> not_pure "A read of a reference"
          end
      | Some (field, false) ->
          State.return
            (R.Expr.field ~loc:l
               (R.Expr.var ~loc:l (name ~loc:l x))
               (qualified_name ~loc:l field))
      | None -> not_pure "This field"
    end
  | Texp_field (record, _, label) ->
      let* field = State.field_of_label ctx.given ~at label in
      begin match field with
      | Some (field, false) ->
          let+ record = pure_in values record in
          R.Expr.field ~loc:l record (qualified_name ~loc:l field)
      | Some (_, true) -> not_pure "A read of a mutable field"
      | None -> not_pure "This field"
      end
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, [ (_, Arg a); (_, Arg b) ])
    when runtime_structural_equality_unsafe ctx path a b ->
      State.of_result
        (error at "Structural equality on values containing references is unsupported")
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, [ (_, Arg a); (_, Arg b) ])
    when is_physical path && not (exact_physical ctx.given.types a b) ->
      not_pure "Physical equality on values that are not immediate"
  | Texp_apply (({ exp_desc = Texp_ident (path, _, declaration); _ } as callee), args) ->
    begin
      let* args = State.of_result (plain_args ~at args) in
      let* () =
        if polymorphic_ordering ctx path args then
          State.of_result (unsupported at "Ordering on polymorphic values")
        else State.return ()
      in
      let* args = State.all args ~f:(pure_in values) in
      match (binop_of_path path, unop_of_path path, path, args) with
      | Some Div, _, _, [ a; b ] ->
          State.return (prelude_call ~loc:l Prelude.div [ a; b ])
      | Some Mod, _, _, [ a; b ] ->
          State.return (prelude_call ~loc:l Prelude.mod_ [ a; b ])
      | Some op, _, _, [ a; b ] -> State.return (R.Expr.binary ~loc:l op a b)
      | _, Some `Not, _, [ a ] -> State.return (R.Expr.not_ ~loc:l a)
      | _, Some `Neg, _, [ a ] -> State.return (R.Expr.neg ~loc:l a)
      | None, None, path, _ ->
          let* path = State.of_result (Source.normalize_value_path e.exp_env ~at path) in
          begin match Path_bindings.find funcs path with
          | Some f ->
              let prefix, captured, role =
                Option.value
                  (List.Assoc.find ctx.given.lifted f ~equal:String.equal)
                  ~default:(0, [], None)
              in
              let* () =
                if prefix = 0 && Option.is_none role then State.return ()
                else not_pure "A continuation call"
              in
              let* captured =
                State.of_result (captured_arguments ~at ~values names captured)
              in
              let+ actual_target =
                State.polymorphic_call ctx ~at ~path ~declaration:declaration.val_type
                  ~occurrence:callee.exp_type ~target:f
              in
              R.Expr.call ~loc:l (qualified_name ~loc:l actual_target) (captured @ args)
          | None -> not_pure ("A call of " ^ Path.name path)
          end
      | _ -> not_pure "This application"
    end
  | Texp_ifthenelse (c, a, Some b) ->
      let* c = pure_in values c in
      let* a = pure_in values a in
      let+ b = pure_in values b in
      R.Expr.ite ~loc:l c a b
  | Texp_let (_, [ { vb_pat = { pat_desc = Tpat_var (id, _, _); _ }; _ } ], body)
    when Path_bindings.mem funcs (Path.Pident id) ->
      pure_in values body
  | Texp_let
      ( Nonrecursive,
        [ { vb_pat = { pat_desc = Tpat_var (id, _, _); _ }; vb_expr; _ } ],
        body ) ->
      let* v = pure_in values vb_expr in
      pure_in ((Ident.unique_name id, v) :: values) body
  | Texp_match (scrutinee, _, [], Total)
    when match Datatypes.desc ctx.given.types scrutinee.exp_type with
         | Tconstr (path, _, _) ->
             Option.exists (Datatypes.find ctx.given.types path) ~f:(fun data ->
                 data.empty)
         | _ -> false ->
      raw_default ctx ~at e.exp_type
  | Texp_match (scrutinee, cases, [], Total) -> begin
      let* v = pure_in values scrutinee in
      let* cases =
        State.all cases ~f:(fun (c : Typedtree.computation Typedtree.case) ->
            match (Typedtree.split_pattern c.c_lhs, c.c_guard) with
            | (Some p, None), None -> State.return (p, c.c_rhs)
            | _ -> not_pure "A guard or an exception case")
      in
      let with_binds binds =
        List.fold binds ~init:values ~f:(fun values (id, value, _) ->
            (Ident.unique_name id, value) :: values)
      in
      let* flat = flat_cases ctx v cases in
      match flat with
      | Some flat ->
          let+ cases =
            State.all flat ~f:(fun (case, binds, _, rhs, _) ->
                let+ body = pure_in (with_binds binds) rhs in
                (case, body))
          in
          begin match cases with
          | [ (R.Expr.Default, body) ] -> body
          | _ -> R.Expr.match_ ~loc:l v cases
          end
      | None ->
          (* OCaml found the cases exhaustive, so the last one needs no test. *)
          let rec chain = function
            | [] -> not_pure "An empty match"
            | [ (p, rhs) ] ->
                let* access, _, binds = pattern ctx p v in
                if List.is_empty access then pure_in (with_binds binds) rhs
                else not_pure "A pattern reading a mutable field"
            | (p, rhs) :: rest -> begin
                let* access, cond, binds = pattern ctx p v in
                if not (List.is_empty access) then
                  not_pure "A pattern reading a mutable field"
                else
                  let* body = pure_in (with_binds binds) rhs in
                  match cond with
                  | None -> State.return body
                  | Some cond ->
                      let+ rest = chain rest in
                      R.Expr.ite ~loc:l cond body rest
              end
          in
          chain cases
    end
  | Texp_match (_, _, _, Partial) -> not_pure "A match that may not be exhaustive"
  | _ -> not_pure "This expression"
