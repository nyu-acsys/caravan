(** OCaml expressions, translated to Raven statements in A-normal form. *)

open Base
open Translate_context
open Proof_terms
open Atomic_proofs

(** The statements evaluating [e], and the value of [e] after them; [tail] if the value is
    the function's result. *)
let rec expr ?(tail = false) ?(continue_state = false) ?(keep_scope = false)
    (ctx : context) (e : Typedtree.expression) :
    (R.Stmt.t list * R.Expr.t, error) Result.t =
  let incoming = ctx.procedure.proof_state and covered = ctx.procedure.return_covered in
  let incoming_names = ctx.procedure.names.scope in
  let key = (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum) in
  let adapter = List.Assoc.find ctx.given.return_proofs key ~equal:Poly.equal in
  let* () =
    match adapter with
    | Some a when not tail ->
        error a.loc "Ghost.returns must follow a normal tail expression"
    | Some a when covered ->
        error a.loc "This return path has more than one Ghost.returns annotation"
    | _ -> Ok ()
  in
  ctx.procedure.return_covered <- covered || Option.is_some adapter;
  let tail_container =
    match e.exp_desc with
    | Texp_let _ | Texp_sequence _ | Texp_match _ -> true
    | Texp_ifthenelse (_, _, Some _) -> true
    | _ -> false
  in
  let* () =
    if
      tail
      && (not ctx.procedure.return_covered)
      && (not tail_container)
      && not (List.is_empty ctx.procedure.ghost_returns)
    then error e.exp_loc "A normal return with ghost results needs Ghost.returns"
    else Ok ()
  in
  let* statements, value = expr_body ~tail ~keep_scope ctx e in
  let* finish =
    match adapter with
    | None -> Ok []
    | Some a -> return_proof ctx a ~result_type:e.exp_type ~result:value
  in
  let* stateful = stateful_access ctx.given.access_proofs e in
  if not (continue_state && stateful) then ctx.procedure.proof_state <- incoming;
  if not keep_scope then ctx.procedure.names.scope <- incoming_names;
  ctx.procedure.return_covered <- covered;
  Ok (statements @ finish, value)

and expr_body ~tail ~keep_scope (ctx : context) (e : Typedtree.expression) :
    (R.Stmt.t list * R.Expr.t, error) Result.t =
  let at = e.exp_loc in
  let l = loc at in
  match e.exp_desc with
  | Texp_ident (Pident id, _, _) -> (
      match Names.find ctx.procedure.names id with
      | Some x -> Ok ([], R.Expr.var ~loc:l (name ~loc:l x))
      | None -> unsupported at "A function used as a value")
  | Texp_ident (path, _, _) -> (
      let* path = Source.normalize_value_path e.exp_env ~at path in
      match Path_bindings.member ctx.given.libraries path with
      | Some member -> Ok ([], R.Expr.call ~loc:l (Qualified_name.raven ~loc:l member) [])
      | None ->
          begin match stdlib_name path with
          | Some "max_int" -> Ok ([], R.Expr.int ~loc:l Prelude.max_int)
          | Some "min_int" -> Ok ([], R.Expr.int ~loc:l Prelude.min_int)
          | _ -> unsupported at "This identifier"
          end)
  | Texp_constant (Const_int n) -> Ok ([], R.Expr.int ~loc:l n)
  | Texp_constant _ -> unsupported at "This constant"
  | Texp_construct ({ txt = Lident "true"; _ }, _, []) -> Ok ([], R.Expr.bool ~loc:l true)
  | Texp_construct ({ txt = Lident "false"; _ }, _, []) ->
      Ok ([], R.Expr.bool ~loc:l false)
  | Texp_construct ({ txt = Lident "()"; _ }, _, []) -> Ok ([], unit_value ~loc:l)
  | Texp_construct (_, cstr, args) ->
      begin match Datatypes.find_cstr ctx.given.types cstr with
      | None -> unsupported at "This constructor"
      | Some (d, c) ->
          let* stmts, args = operands ctx args in
          Ok (stmts, R.Expr.call ~loc:l (Datatypes.ctor_name ~loc:l d c) args)
      end
  | Texp_tuple components ->
      let* stmts, components = operands ctx (List.map components ~f:snd) in
      Ok (stmts, R.Expr.tuple ~loc:l components)
  | Texp_record { fields; extended_expression = None; _ } ->
      let fields = Array.to_list fields in
      let* values =
        all fields ~f:(fun (label, def) ->
            match (def : Typedtree.record_label_definition) with
            | Overridden (_, e) -> Ok (label, e)
            | Kept _ -> unsupported at "This record")
      in
      let* stmts, args = operands ctx (List.map values ~f:snd) in
      let label, _ = List.hd_exn fields in
      begin match Datatypes.find_label ctx.given.types label with
      | Some { heap = Some _; _ } ->
          let* typ = typ ctx ~at e.exp_type in
          let* fields =
            all values ~f:(fun (label, _) ->
                let* field = field_of_label ctx ~at label in
                Ok (fst (Option.value_exn field)))
          in
          let x = Names.fresh ctx.procedure.names "tmp" in
          let views, view_args = view_allocation ctx ~loc:l fields in
          let* explicit = allocation_initializers ctx e in
          let init =
            R.Stmt.new_rhs
              (List.map2_exn fields args ~f:(fun f v -> (qualified_name ~loc:l f, Some v))
              @ view_args @ explicit)
          in
          Ok
            ( stmts @ views @ R.Stmt.local ~loc:l ~typ ~init (ident ~loc:l x),
              R.Expr.var ~loc:l (name ~loc:l x) )
      | Some ({ ctors = [ c ]; _ } as d) ->
          Ok (stmts, R.Expr.call ~loc:l (Datatypes.ctor_name ~loc:l d c) args)
      | _ -> unsupported at "This record"
      end
  | Texp_record _ -> unsupported at "A record copied with changes"
  | Texp_field (record, _, label) -> begin
      let* stmts, v = expr ctx record in
      let* field = field_of_label ctx ~at label in
      match field with
      | Some (field, true) ->
          let* reading, value = ordinary_read ctx ~at ~field ~elt:e.exp_type v in
          Ok (stmts @ reading, value)
      | Some (field, false) ->
          let value = R.Expr.field ~loc:l v (qualified_name ~loc:l field) in
          if is_int e.exp_type then
            let x = Names.fresh ctx.procedure.names "tmp" in
            Ok
              ( stmts
                @ R.Stmt.local ~loc:l ~typ:(R.Type.int ~loc:l)
                    ~init:(R.Stmt.expr_rhs value) (ident ~loc:l x)
                @ assume_in_range ~loc:l e.exp_type x,
                R.Expr.var ~loc:l (name ~loc:l x) )
          else Ok (stmts, value)
      | None -> unsupported at "This field"
    end
  | Texp_setfield (record, _, label, value) -> begin
      let* value_stmts, value = expr ctx value in
      let* record_stmts, record = expr ctx record in
      let* field = field_of_label ctx ~at label in
      match field with
      | Some (field, true) ->
          let* writing = ordinary_write ctx ~at ~field ~elt:label.lbl_arg record value in
          Ok (value_stmts @ record_stmts @ [ writing ], unit_value ~loc:l)
      | _ -> unsupported at "This field"
    end
  | Texp_match (scrutinee, cases, [], partial) ->
      let read = is_read_value ctx scrutinee in
      let* scrutinee_stmts, v = expr ctx scrutinee in
      (* The cases read the scrutinee repeatedly, so it is named unless it is a variable. *)
      let* naming, v =
        match scrutinee.exp_desc with
        | Texp_ident (Pident _, _, _) -> Ok ([], v)
        | _ ->
            let* typ = typ ctx ~at:scrutinee.exp_loc scrutinee.exp_type in
            let x = Names.fresh ctx.procedure.names "scrutinee" in
            Ok
              ( R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs v) (ident ~loc:l x),
                R.Expr.var ~loc:l (name ~loc:l x) )
      in
      let* cases =
        all cases ~f:(fun (c : Typedtree.computation Typedtree.case) ->
            match (Typedtree.split_pattern c.c_lhs, c.c_guard) with
            | (Some p, None), None -> Ok (p, c.c_rhs)
            | _, Some guard -> unsupported guard.exp_loc "A guard"
            | _ -> unsupported c.c_lhs.pat_loc "An exception case")
      in
      let total = match partial with Total -> true | Partial -> false in
      (* A match on the value of a read that left the atomic update open closes it. *)
      let commits =
        match au_state ctx with
        | Some (On_read c) when read -> Some (case_commits c (List.map cases ~f:fst))
        | _ -> None
      in
      let* stmts =
        branch ctx e (fun target ->
            match_cases ?commits ~tail ctx ~at v cases ~total target)
      in
      Ok (scrutinee_stmts @ naming @ fst stmts, snd stmts)
  | Texp_match (_, _, _ :: _, _) -> unsupported at "An effect handler"
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, args) ->
      let* args = plain_args ~at args in
      apply ctx e path args
  | Texp_apply _ -> unsupported at "This application"
  | Texp_ifthenelse (c, e1, e2) ->
      let polarity = cas_polarity ctx c in
      let* c_stmts, c = expr ctx c in
      let* stmts =
        branch ctx e (fun target -> conditional ctx ~at ?polarity ~tail c e1 e2 target)
      in
      Ok (c_stmts @ fst stmts, snd stmts)
  | Texp_let (_, [ { vb_pat = { pat_desc = Tpat_var (id, _, _); _ }; _ } ], rest)
    when Path_bindings.mem ctx.given.functions (Path.Pident id) ->
      (* A local function, lifted to the top level. *)
      expr ~tail ~keep_scope ctx rest
  | Texp_let (Nonrecursive, bindings, body) ->
      (* The bound expressions are evaluated before any of their variables is bound. *)
      let* evaluated =
        all bindings ~f:(fun (vb : Typedtree.value_binding) ->
            let polarity = cas_polarity ctx vb.vb_expr in
            let read = is_read_value ctx vb.vb_expr in
            let* stmts, v =
              expr ~continue_state:(List.length bindings = 1) ctx vb.vb_expr
            in
            begin match (ctx.procedure.au, polarity, vb.vb_pat.pat_desc) with
            | Some au, Some p, Tpat_var (id, _, _) ->
                au.cas_results <- (Ident.unique_name id, p) :: au.cas_results
            | Some au, None, Tpat_var (id, _, _) when read ->
                au.read_results <- Ident.unique_name id :: au.read_results
            | _ -> ()
            end;
            Ok (vb, stmts, v))
      in
      let* defs =
        all evaluated ~f:(fun ((vb : Typedtree.value_binding), _, v) ->
            let* reading, cond, binds = pattern ctx vb.vb_pat v in
            match cond with
            | Some _ ->
                unsupported vb.vb_pat.pat_loc "A refutable pattern in a let binding"
            | None ->
                let* defs =
                  all binds ~f:(fun (id, value, t) ->
                      let* typ = typ ctx ~at t in
                      let x = Names.bind ~typ:t ctx.procedure.names id in
                      Ok
                        (R.Stmt.local ~loc:l ~const:true ~typ
                           ~init:(R.Stmt.expr_rhs value) (ident ~loc:l x)
                        @ assume_in_range ~loc:l t x))
                in
                Ok (reading @ List.concat defs))
      in
      let last = List.last_exn bindings in
      let* ghost =
        ghost ctx ~after:last.vb_expr.exp_loc.loc_end ~before:body.exp_loc.loc_start
      in
      let* body_stmts, body = expr ~tail ~keep_scope ctx body in
      Ok
        ( List.concat_map evaluated ~f:(fun (_, stmts, _) -> stmts)
          @ List.concat defs @ ghost @ body_stmts,
          body )
  | Texp_let (Recursive, _, _) -> unsupported at "A local recursive function"
  | Texp_sequence (e1, e2) ->
      let* stmts1, _ = expr ~continue_state:true ctx e1 in
      let* ghost = ghost ctx ~after:e1.exp_loc.loc_end ~before:e2.exp_loc.loc_start in
      let* stmts2, v = expr ~tail ~keep_scope ctx e2 in
      Ok (stmts1 @ ghost @ stmts2, v)
  | Texp_while (cond, body) ->
      let* () = no_loop_before_linearizing ctx ~at in
      let* spec = loop_spec ctx ~after:cond.exp_loc body in
      let* c_stmts, c = expr ctx cond in
      let x = Names.fresh ctx.procedure.names "continue" in
      (* A condition that needs statements, as reads, is evaluated before the loop and at the
         end of each iteration, into [x]; the invariant relates [x] to the values it owns,
         if the condition can be expressed in them. *)
      let relation reads =
        if List.is_empty c_stmts then Ok None
        else
          match pure ~reads ctx ~funcs:Path_bindings.empty [] cond with
          | Ok c ->
              Ok (Some (R.Expr.binary ~loc:l Eq (R.Expr.var ~loc:l (name ~loc:l x)) c))
          | Error _ -> Ok None
      in
      let* invariants = loop_invariants ctx ~at spec ~relation in
      let* body_stmts, _ = expr ctx body in
      if List.is_empty c_stmts then
        Ok ([ R.Stmt.while_ ~loc:l ~invariants c body_stmts ], unit_value ~loc:l)
      else
        let target = (x, l) in
        let* c_stmts', c' = expr ctx cond in
        Ok
          ( c_stmts
            @ R.Stmt.local ~loc:l ~const:false ~typ:(R.Type.bool ~loc:l) (ident ~loc:l x)
            @ [
                assign target c;
                R.Stmt.while_ ~loc:l ~invariants
                  (R.Expr.var ~loc:l (name ~loc:l x))
                  (body_stmts @ c_stmts' @ [ assign target c' ]);
              ],
            unit_value ~loc:l )
  | Texp_for (id, _, lo, hi, direction, body) ->
      let* () = no_loop_before_linearizing ctx ~at in
      let* spec = loop_spec ctx ~after:hi.exp_loc body in
      let* lo_stmts, lo = expr ctx lo in
      let* hi_stmts, hi = expr ctx hi in
      let int = R.Type.int ~loc:l in
      (* A bound, evaluated once into a variable, which the invariant says it equals, as the
         value is an expression of immutable variables. *)
      let bound base v =
        let x = Names.fresh ctx.procedure.names base in
        let var = R.Expr.var ~loc:l (name ~loc:l x) in
        ( R.Stmt.local ~loc:l ~typ:int ~init:(R.Stmt.expr_rhs v) (ident ~loc:l x),
          var,
          R.Spec.make (R.Expr.binary ~loc:l Eq var v) )
      in
      let lo_def, lo, lo_value = bound "first" lo in
      let hi_def, hi, hi_value = bound "last" hi in
      let i = Names.bind ~typ:Predef.type_int ctx.procedure.names id in
      let iv = R.Expr.var ~loc:l (name ~loc:l i) in
      let* invariants =
        loop_invariants ~counter:i ctx ~at spec ~relation:(fun _ -> Ok None)
      in
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
      let* body_stmts, _ = expr ctx body in
      Ok
        ( lo_stmts @ hi_stmts @ lo_def @ hi_def
          @ R.Stmt.local ~loc:l ~const:false ~typ:int ~init:(R.Stmt.expr_rhs lo)
              (ident ~loc:l i)
          @ [
              R.Stmt.while_ ~loc:l
                ~invariants:(R.Spec.make range :: lo_value :: hi_value :: invariants)
                test
                (body_stmts @ [ assign (i, l) step ]);
            ],
          unit_value ~loc:l )
  | Texp_assert (c, _) ->
      let* stmts, c = expr ctx c in
      Ok (stmts @ [ R.Stmt.assert_ ~loc:l (R.Spec.make c) ], unit_value ~loc:l)
  | _ -> unsupported at "This expression"

(** The application of the function at [path] to [args], in [e]. *)
and apply ctx (e : Typedtree.expression) (path : Path.t)
    (args : Typedtree.expression list) =
  let at = e.exp_loc in
  let l = loc at in
  let contents (r : Typedtree.expression) =
    match Datatypes.desc ctx.given.types r.exp_type with
    | Tconstr (_, [ elt ], _) -> ref_field ctx ~at elt
    | _ -> unsupported at "This reference"
  in
  (* The value of the field [field] of the reference [r], read into a variable. *)
  let read r field typ_of = ordinary_read ctx ~at ~field ~elt:typ_of r in
  match (stdlib_name path, args) with
  | _ when Option.is_some (atomic_name path) ->
      atomic ctx e (Option.value_exn (atomic_name path)) args
  | Some "ref", [ v ] ->
      let* field = ref_field ctx ~at v.exp_type in
      let* stmts, v = expr ctx v in
      let x = Names.fresh ctx.procedure.names "tmp" in
      let views, view_args = view_allocation ctx ~loc:l [ field ] in
      let* explicit = allocation_initializers ctx e in
      let init =
        R.Stmt.new_rhs ((qualified_name ~loc:l field, Some v) :: (view_args @ explicit))
      in
      Ok
        ( stmts @ views
          @ R.Stmt.local ~loc:l ~typ:(R.Type.ref ~loc:l) ~init (ident ~loc:l x),
          R.Expr.var ~loc:l (name ~loc:l x) )
  | Some "!", [ r ] ->
      let* field = contents r in
      let* stmts, r = expr ctx r in
      let* reading, v = read r field e.exp_type in
      Ok (stmts @ reading, v)
  | Some ":=", [ r; v ] ->
      let* field = contents r in
      let elt = v.exp_type in
      let* v_stmts, v = expr ctx v in
      let* r_stmts, r = expr ctx r in
      let* writing = ordinary_write ctx ~at ~field ~elt r v in
      Ok (v_stmts @ r_stmts @ [ writing ], unit_value ~loc:l)
  | Some (("incr" | "decr") as op), [ r ] ->
      let* field = contents r in
      let* stmts, r = expr ctx r in
      let int_type = Predef.type_int in
      let* reading, v = read r field int_type in
      let binop : R.Expr.binop = if String.equal op "incr" then Plus else Minus in
      let v' = R.Expr.binary ~loc:l binop v (R.Expr.int ~loc:l 1) in
      let what = if String.equal op "incr" then "increment" else "decrement" in
      let* writing = ordinary_write ctx ~at ~field ~elt:int_type r v' in
      Ok (stmts @ reading @ [ no_overflow ctx ~at what v'; writing ], unit_value ~loc:l)
  | _ -> apply_operator ctx e path args

(** The application of [Atomic.op] to [args], in [e]. *)
and atomic ctx (e : Typedtree.expression) op (args : Typedtree.expression list) =
  let at = e.exp_loc in
  let l = loc at in
  let element (t : Types.type_expr) =
    match Datatypes.desc ctx.given.types t with
    | Tconstr (_, [ elt ], _) -> Ok elt
    | _ -> unsupported at "This atomic"
  in
  (* How the step linearizes the function: as its annotation says, or by default. *)
  let* annotation = linearization ctx e in
  let how default =
    match (annotation, default) with
    | None, _ -> Ok default
    | Some (S.Performs a), _ ->
        begin match named_action ctx a with
        | Some performed ->
            Option.iter ctx.procedure.au ~f:(fun au ->
                au.performing <- Some ({ performed; bindings = [] }, None));
            Ok default
        | None -> error a.pid_loc (Printf.sprintf "There is no action %s" a.pid_str)
        end
    | Some S.Commit, _ -> Ok `Commit
    | Some (Returning ({ pat_desc = Pconstr (Qid c, _); _ }, Commits)), `Abort ->
        Ok (`Returning c.pid_str)
    | Some (Returning (p, Commits)), `Abort ->
        unsupported p.pat_loc "A pattern other than a constructor, after returning,"
    | Some (Returning (p, o)), `Abort -> Ok (`Decide (p, o))
    | Some (Returning (p, _)), _ ->
        error p.pat_loc "Only a read can linearize by its value"
  in
  (* The result of [f] applied to the atomic and [args], in a variable, a step that
     linearizes the function by default as [default] says. *)
  let result ?(default = `Commit) ?op f atomic args =
    let* typ = typ ctx ~at e.exp_type in
    let x = Names.fresh ctx.procedure.names "tmp" in
    let v = R.Expr.var ~loc:l (name ~loc:l x) in
    let init =
      R.Stmt.expr_rhs (R.Expr.call ~loc:l (qualified_name ~loc:l f) (atomic :: args))
    in
    let* how = how default in
    let step = Option.map op ~f:(fun (op, field) -> (op, field, atomic, args, v)) in
    let* step =
      linearize ?step ~value:v ~access_type:e.exp_type ctx ~at how
        (R.Stmt.local ~loc:l ~typ ~init (ident ~loc:l x))
    in
    Ok (step, v)
  in
  let* elt =
    match args with
    | a :: _ when not (String.is_prefix op ~prefix:"make") -> element a.exp_type
    | _ -> element e.exp_type
  in
  let* field = atomic_field ctx ~at elt in
  let* nested = nested_stateful_read ctx.given.access_proofs e in
  let* stmts, values =
    match nested with
    | Some argument ->
        let* stmts, value = expr ~continue_state:true ctx argument in
        Ok (stmts, [ value ])
    | None -> operands ctx args
  in
  let primitive op = primitive ctx ~at elt op in
  match (op, values) with
  | ("make" | "make_contended"), [ v ] ->
      let x = Names.fresh ctx.procedure.names "tmp" in
      let views, view_args = view_allocation ctx ~loc:l [ field ] in
      let* explicit = allocation_initializers ctx e in
      let init =
        R.Stmt.new_rhs ((qualified_name ~loc:l field, Some v) :: (view_args @ explicit))
      in
      Ok
        ( stmts @ views
          @ R.Stmt.local ~loc:l ~typ:(R.Type.ref ~loc:l) ~init (ident ~loc:l x),
          R.Expr.var ~loc:l (name ~loc:l x) )
  | "get", [ a ] ->
      let* typ = typ ctx ~at e.exp_type in
      let x = Names.fresh ctx.procedure.names "tmp" in
      let read = R.Stmt.expr_rhs (R.Expr.field ~loc:l a (qualified_name ~loc:l field)) in
      let* how = how `Abort in
      let value = R.Expr.var ~loc:l (name ~loc:l x) in
      let* step =
        linearize ~value ~access_type:e.exp_type ctx ~at how
          (R.Stmt.local ~loc:l ~typ ~init:read (ident ~loc:l x))
      in
      record_read ctx ~atomic:a value;
      Ok (stmts @ step, R.Expr.var ~loc:l (name ~loc:l x))
  | "set", [ a; v ] ->
      let* how = how `Commit in
      let* step =
        linearize ~value:(unit_value ~loc:l) ~access_type:e.exp_type ctx ~at how
          [ write ~loc:l a field v ]
      in
      Ok (stmts @ step, unit_value ~loc:l)
  | "exchange", [ a; v ] ->
      let* f = primitive Exchange in
      let* reading, r = result f a [ v ] in
      Ok (stmts @ reading, r)
  | "compare_and_set", [ a; old_val; new_val ] ->
      let* f = primitive Compare_and_set in
      let* reading, r =
        result ~default:`Cas ~op:("compare_and_set", field) f a [ old_val; new_val ]
      in
      Ok (stmts @ reading, r)
  | "fetch_and_add", [ a; n ] ->
      let* f = primitive Fetch_and_add in
      let* reading, r = result f a [ n ] in
      Ok (stmts @ reading, r)
  | (("incr" | "decr") as op), [ a ] ->
      let* f = primitive Fetch_and_add in
      let x = Names.fresh ctx.procedure.names "tmp" in
      let n = R.Expr.int ~loc:l (if String.equal op "incr" then 1 else -1) in
      let init = R.Stmt.expr_rhs (R.Expr.call ~loc:l (name ~loc:l f) [ a; n ]) in
      let* how = how `Commit in
      let* step =
        linearize ~value:(unit_value ~loc:l) ~access_type:e.exp_type ctx ~at how
          (R.Stmt.local ~loc:l ~typ:(R.Type.int ~loc:l) ~init (ident ~loc:l x))
      in
      Ok (stmts @ step, unit_value ~loc:l)
  | _ -> unsupported at ("Atomic." ^ op)

(** The application of the operator or function at [path] to [args], in [e]. *)
and apply_operator ctx (e : Typedtree.expression) (path : Path.t)
    (args : Typedtree.expression list) =
  let at = e.exp_loc in
  let l = loc at in
  match (binop_of_path path, unop_of_path path, args) with
  | Some (Eq | Neq), _, [ a; b ] when runtime_structural_equality_unsafe ctx path a b ->
      error at "Structural equality on values containing references is unsupported"
  | Some ((And | Or) as op), _, [ a; b ] ->
      (* The right operand is evaluated only if the left one does not decide. *)
      let* a_stmts, a = expr ctx a in
      let before = ctx.procedure.snapshots
      and before_positions = ctx.procedure.positions in
      let* b_stmts, b = expr ctx b in
      (* The snapshots that the right operand takes are on one path only. *)
      ctx.procedure.snapshots <- common_snapshots [ before; ctx.procedure.snapshots ];
      ctx.procedure.positions <- before_positions;
      if List.is_empty b_stmts then Ok (a_stmts, R.Expr.binary ~loc:l op a b)
      else
        let then_, else_ =
          match op with And -> (`Rhs, `Value false) | _ -> (`Value true, `Rhs)
        in
        let* stmts, v =
          branch ctx e (fun target ->
              let target = Option.value_exn target in
              let arm = function
                | `Rhs -> b_stmts @ [ assign target b ]
                | `Value v -> [ assign target (R.Expr.bool ~loc:l v) ]
              in
              Ok [ R.Stmt.if_ ~loc:l a (arm then_) (arm else_) ])
        in
        Ok (a_stmts @ stmts, v)
  | Some ((Eq | Neq) as op), _, [ a; b ]
    when is_physical path && not (exact_physical ctx.given.types a b) ->
      let* b_stmts, b = expr ctx b in
      let* a_stmts, a = expr ctx a in
      let x = Names.fresh ctx.procedure.names "same" in
      let same = R.Expr.var ~loc:l (name ~loc:l x) in
      Ok
        ( b_stmts @ a_stmts
          @ R.Stmt.local ~loc:l ~typ:(R.Type.bool ~loc:l) (ident ~loc:l x)
          @ [
              R.Stmt.havoc ~loc:l (name ~loc:l x);
              R.Stmt.assume ~loc:l
                (R.Spec.make
                   (R.Expr.binary ~loc:l Impl same (R.Expr.binary ~loc:l Eq a b)));
            ],
          match op with Eq -> same | _ -> R.Expr.not_ ~loc:l same )
  | Some op, _, [ a; b ] ->
      let divisor = b.exp_loc in
      let* b_stmts, b = expr ctx b in
      let* a_stmts, a = expr ctx a in
      let stmts = b_stmts @ a_stmts in
      let nonzero () =
        check ctx ~at:divisor "This divisor may be zero"
          (R.Expr.binary ~loc:(loc divisor) Neq b (R.Expr.int ~loc:(loc divisor) 0))
      in
      let checked what v = Ok (stmts @ [ no_overflow ctx ~at what v ], v) in
      begin match op with
      | Plus -> checked "addition" (R.Expr.binary ~loc:l op a b)
      | Minus -> checked "subtraction" (R.Expr.binary ~loc:l op a b)
      | Mult -> checked "multiplication" (R.Expr.binary ~loc:l op a b)
      | Div ->
          let v = prelude_call ~loc:l Prelude.div [ a; b ] in
          let nonzero = nonzero () in
          Ok (stmts @ [ nonzero; no_overflow ctx ~at "division" v ], v)
      | Mod ->
          let nonzero = nonzero () in
          Ok (stmts @ [ nonzero ], prelude_call ~loc:l Prelude.mod_ [ a; b ])
      | _ -> Ok (stmts, R.Expr.binary ~loc:l op a b)
      end
  | _, Some op, [ a ] -> (
      let* stmts, a = expr ctx a in
      match op with
      | `Not -> Ok (stmts, R.Expr.not_ ~loc:l a)
      | `Neg ->
          let v = R.Expr.neg ~loc:l a in
          Ok (stmts @ [ no_overflow ctx ~at "negation" v ], v))
  | None, None, _ -> (
      let* path = Source.normalize_value_path e.exp_env ~at path in
      match resolved_call ctx.given.functions ctx.given.libraries path with
      | Some f -> call ctx e f args
      | None -> (
          match path with
          | Pident _ -> unsupported at "A call of a local function"
          | _ -> unsupported at ("A call of " ^ Path.name path)))
  | _ -> unsupported at "This application"

(** The call of the top-level function [f] with [args], in [e]: a statement, whose result
    is kept in a variable unless it is unit. *)
and call ctx (e : Typedtree.expression) f (ocaml_args : Typedtree.expression list) =
  let* arguments, args = operands ctx ocaml_args in
  let signature = List.Assoc.find ctx.given.procedure_signatures f ~equal:String.equal in
  let inputs = Option.value_map signature ~default:[] ~f:(fun s -> s.procedure_inputs) in
  let outputs =
    Option.value_map signature ~default:[] ~f:(fun s -> s.procedure_outputs)
  in
  let run explicit =
    call_prepared ctx e f ocaml_args args ~explicit ~signature_outputs:outputs
  in
  let annotation =
    List.Assoc.find ctx.given.access_proofs
      (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum)
      ~equal:Poly.equal
  in
  match annotation with
  | None ->
      let* statements, value, _ = run None in
      Ok (arguments @ statements, value)
  | Some annotation ->
      let result = ref None in
      let* statements =
        access_proof ctx annotation ~result_type:e.exp_type
          ~input_types:(List.map inputs ~f:snd) ~output_types:(List.map outputs ~f:snd)
          (fun values ->
            let* statements, value, outputs = run (Some values) in
            result := Some value;
            Ok (statements, value, outputs))
      in
      begin match !result with
      | Some value -> Ok (arguments @ statements, value)
      | None -> error annotation.loc "The scope did not invoke its attached call"
      end

and call_prepared ctx (e : Typedtree.expression) f ocaml_args args ~explicit
    ~signature_outputs =
  let l = loc e.exp_loc in
  let stmts = [] in
  (* A lifted local function takes the parameters of the function it continues first. *)
  let prefix, captured, role =
    Option.value
      (List.Assoc.find ctx.given.lifted f ~equal:String.equal)
      ~default:(0, [], None)
  in
  let* prefix =
    if List.length ctx.procedure.formals >= prefix then
      Ok (List.take ctx.procedure.formals prefix)
    else error e.exp_loc "This call needs the parameters of the function it continues"
  in
  let* captured =
    all captured ~f:(fun x ->
        match Names.find ctx.procedure.names x with
        | Some y -> Ok (R.Expr.var ~loc:l (name ~loc:l y))
        | None ->
            error e.exp_loc (Printf.sprintf "%s is not in scope here" (Ident.name x)))
  in
  let prefix = prefix @ captured in
  (* A ghost argument is the value of which the argument a precondition relates it to is a
     field, as [q] for [tail] in [fix_tail tail new_tail] after [push { tail; _ }]. *)
  let* ghosts =
    match explicit with
    | Some values -> Ok values
    | None ->
        all
          (Option.value
             (List.Assoc.find ctx.given.ghost_args f ~equal:String.equal)
             ~default:[])
          ~f:(fun equation ->
            let known =
              Option.bind equation ~f:(fun (i, field) ->
                  match List.nth ocaml_args (i - List.length prefix) with
                  | Some { exp_desc = Texp_ident (Pident id, _, _); _ } ->
                      Option.bind (Names.find ctx.procedure.names id) ~f:(fun x ->
                          List.find_map ctx.procedure.fields_of ~f:(fun (y, (g, value)) ->
                              Option.some_if
                                (String.equal x y && String.equal g field)
                                value))
                  | _ -> None)
            in
            match (known, equation) with
            | Some value, _ -> Ok value
            | None, None ->
                error e.exp_loc
                  "Caravan cannot tell the ghost argument of this call: give the callee \
                   a precondition that makes a parameter a field of it, as tail = q.tail"
            | None, Some (_, field) ->
                error e.exp_loc
                  (Printf.sprintf
                     "Caravan cannot tell the ghost argument of this call: the argument \
                      is not a variable known to be the field %s of a value, as one a \
                      record pattern binds"
                     field))
  in
  let args = prefix @ args @ ghosts in
  (* A recursive call before the function linearizes is a retry, which linearizes it in
     its place, with the atomic update's values of the implicit parameters, as does a call
     of a function that continues the update. *)
  let* retry =
    match ctx.procedure.au with
    | Some au
      when String.equal au.self f || Option.exists role ~f:(fun r -> Ident.same r au.role)
      ->
        begin match au.state with
        | Pending ->
            let* opening, values = au.open_ ~at:e.exp_loc ~unfold:false in
            au.values <- values;
            au.step <- e.exp_loc;
            au.state <- Committed;
            Ok (Some (au, opening, values))
        | Committed -> Ok None
        | Committing | On_cas | On_read _ | Partly | Registered _ | Unknown ->
            error e.exp_loc
              "Caravan cannot tell whether the function has linearized before this call"
        end
    | _ -> Ok None
  in
  let opening, implicit =
    Option.value_map retry ~default:([], []) ~f:(fun (_, o, values) -> (o, values))
  in
  (* The retry commits with its result. *)
  let closing value =
    Option.value_map retry ~default:(Ok []) ~f:(fun (au, _, _) ->
        au.close Commit_call ~value)
  in
  (* The latest snapshot witnesses the facts about earlier states that the callee
     requires, with the arguments' positions in it. *)
  let* witnesses =
    all
      (Option.value (List.Assoc.find ctx.given.pasts f ~equal:String.equal) ~default:[])
      ~f:(fun (inv, field, i) ->
        let structure =
          List.find ctx.given.shared.structures ~f:(fun st ->
              String.equal st.invariant inv)
        in
        match
          (structure, List.Assoc.find ctx.procedure.snapshots inv ~equal:String.equal)
        with
        | _ when Option.is_some (known_position ctx inv field (List.nth_exn args i)) ->
            let p =
              Option.value_exn (known_position ctx inv field (List.nth_exn args i))
            in
            Ok [ p.pos_snapshot; p.pos_k ]
        | Some st, Some (latest :: _) ->
            let index = List.Assoc.find_exn latest.indices field ~equal:String.equal in
            Ok
              [
                state_of ~loc:l st (grown st latest.values);
                R.Expr.index ~loc:l index (List.nth_exn args i);
              ]
        | _ ->
            error e.exp_loc
              "This call needs a fact about an earlier state, of which no snapshot was \
               taken")
  in
  (* A library's procedure is qualified by its module, as [Backoff.once]. *)
  let callee_name = qualified_name ~loc:l f in
  let callee = R.Expr.call ~loc:l callee_name (args @ List.concat witnesses @ implicit) in
  (* The ghost results witnessing facts about the state after the call: the caller's own,
     if the callee continues its update with the same ones. *)
  let ghost_facts =
    Option.value
      (List.Assoc.find ctx.given.past_returns f ~equal:String.equal)
      ~default:[]
  in
  let ghost_count = 2 * List.length ghost_facts in
  let ghost_decls, ghosts =
    match retry with
    | Some (au, _, _) when ghost_count > 0 && List.length au.ghost_results = ghost_count
      ->
        ([], au.ghost_results)
    | _ ->
        let fresh =
          List.concat_map ghost_facts ~f:(fun (inv, _, _) ->
              let st =
                List.find_exn ctx.given.shared.structures ~f:(fun st ->
                    String.equal st.invariant inv)
              in
              [
                ( Names.fresh ctx.procedure.names "snapshot",
                  R.Type.named ~loc:l
                    (generated_module_member ~loc:l (module_name st "state") "T")
                    [] );
                (Names.fresh ctx.procedure.names "position", R.Type.int ~loc:l);
              ])
        in
        ( List.concat_map fresh ~f:(fun (x, typ) ->
              R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x)),
          List.map fresh ~f:(fun (x, _) -> R.Expr.var ~loc:l (name ~loc:l x)) )
  in
  (* The ghost results witness the positions of the entries the callee ensures. *)
  let rec witnessed facts ghosts =
    match (facts, ghosts) with
    | (inv, field, entry) :: facts, snapshot :: k :: ghosts ->
        let rest = witnessed facts ghosts in
        begin match entry args with
        | Some e ->
            {
              pos_inv = inv;
              pos_field = field;
              pos_element = e;
              pos_snapshot = snapshot;
              pos_k = k;
            }
            :: rest
        | None -> rest
        end
    | _ -> []
  in
  ctx.procedure.positions <- witnessed ghost_facts ghosts @ ctx.procedure.positions;
  let* public =
    all signature_outputs ~f:(fun (_, ty) ->
        let raven = Names.fresh ctx.procedure.names "ghost_result" in
        let* raven_type = typ ctx ~at:e.exp_loc ty in
        Ok
          ( R.Expr.var ~loc:l (name ~loc:l raven),
            R.Stmt.local ~loc:l ~ghost:true ~typ:raven_type (ident ~loc:l raven) ))
  in
  let public_values = List.map public ~f:fst in
  let ghost_decls = List.concat_map public ~f:snd @ ghost_decls in
  let ghosts = public_values @ ghosts in
  if is_unit e.exp_type then
    let* closing = closing (unit_value ~loc:l) in
    let call =
      match ghosts with
      | [] -> [ R.Stmt.call ~loc:l callee ]
      | _ -> ghost_decls @ [ R.Stmt.assign ~loc:l ghosts (R.Stmt.expr_rhs callee) ]
    in
    Ok (stmts @ opening @ call @ closing, unit_value ~loc:l, public_values)
  else
    let* typ = typ ctx ~at:e.exp_loc e.exp_type in
    let x = Names.fresh ctx.procedure.names "tmp" in
    let v = R.Expr.var ~loc:l (name ~loc:l x) in
    let def =
      match ghosts with
      | [] -> R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs callee) (ident ~loc:l x)
      | _ ->
          R.Stmt.local ~loc:l ~typ (ident ~loc:l x)
          @ ghost_decls
          @ [ R.Stmt.assign ~loc:l (v :: ghosts) (R.Stmt.expr_rhs callee) ]
    in
    let* closing = closing v in
    Ok (stmts @ opening @ def @ closing, v, public_values)

(** The statements evaluating [args], right to left as OCaml does, and their values. *)
and operands ctx (args : Typedtree.expression list) =
  let* evaluated = all (List.rev args) ~f:(fun arg -> expr ctx arg) in
  Ok (List.concat_map evaluated ~f:fst, List.rev_map evaluated ~f:snd)

(** The accesses and condition for matching [p] against [v], and its bindings. *)
and pattern ?guard ctx (p : Typedtree.pattern) (v : R.Expr.t) =
  let at = p.pat_loc in
  let l = loc at in
  let conjoin conds =
    List.reduce (List.filter_opt conds) ~f:(fun a b -> R.Expr.binary ~loc:l And a b)
  in
  let components guard ps values =
    let* matched =
      all (List.zip_exn ps values) ~f:(fun (p, (access, v)) ->
          let* nested, cond, binds = pattern ?guard ctx p v in
          Ok (access @ nested, cond, binds))
    in
    Ok
      ( List.concat_map matched ~f:(fun (access, _, _) -> access),
        conjoin (List.map matched ~f:(fun (_, cond, _) -> cond)),
        List.concat_map matched ~f:(fun (_, _, binds) -> binds) )
  in
  match p.pat_desc with
  | Tpat_any -> Ok ([], None, [])
  | Tpat_var (id, _, _) -> Ok ([], None, [ (id, v, p.pat_type) ])
  | Tpat_alias (q, id, _, _, _) ->
      let* access, cond, binds = pattern ?guard ctx q v in
      Ok (access, cond, binds @ [ (id, v, p.pat_type) ])
  | Tpat_constant (Const_int n) ->
      Ok ([], Some (R.Expr.binary ~loc:l Eq v (R.Expr.int ~loc:l n)), [])
  | Tpat_tuple ps ->
      let values = List.mapi ps ~f:(fun i _ -> ([], R.Expr.tuple_get ~loc:l v i)) in
      components guard (List.map ps ~f:snd) values
  | Tpat_record (fields, _) ->
      let* parts =
        all fields ~f:(fun (_, label, p) ->
            let* field = field_of_label ctx ~at label in
            match field with
            | Some (field, false) ->
                Ok (p, ([], R.Expr.field ~loc:l v (qualified_name ~loc:l field)))
            | Some (field, true) ->
                let* access, value =
                  ordinary_read ?guard ctx ~at ~field ~elt:label.lbl_arg v
                in
                Ok (p, (access, value))
            | None -> unsupported at "This field")
      in
      components guard (List.map parts ~f:fst) (List.map parts ~f:snd)
  | Tpat_construct (_, { cstr_name = ("true" | "false") as b; _ }, [], _) ->
      Ok
        ( [],
          Some (R.Expr.binary ~loc:l Eq v (R.Expr.bool ~loc:l (String.equal b "true"))),
          [] )
  | Tpat_construct (_, { cstr_name = "()"; _ }, [], _) -> Ok ([], None, [])
  | Tpat_construct (_, cstr, ps, _) ->
      begin match Datatypes.find_cstr ctx.given.types cstr with
      | None -> unsupported at "This constructor"
      | Some (_, c) ->
          let is_c = R.Expr.is_ ~loc:l v (ident ~loc:l c.raven) in
          let fields =
            List.map c.fields ~f:(fun f ->
                ([], R.Expr.field ~loc:l v (qualified_name ~loc:l f)))
          in
          let* access, cond, binds =
            components (conjoin [ guard; Some is_c ]) ps fields
          in
          Ok (access, conjoin [ Some is_c; cond ], binds)
      end
  | Tpat_or (p1, p2, _) -> begin
      let* a1, c1, b1 = pattern ?guard ctx p1 v in
      let* a2, c2, b2 = pattern ?guard ctx p2 v in
      match (a1, a2, c1, c2, b1, b2) with
      | [], [], Some c1, Some c2, [], [] ->
          Ok ([], Some (R.Expr.binary ~loc:l Or c1 c2), [])
      | [], [], _, _, [], [] -> Ok ([], None, [])
      | _ :: _, _, _, _, _, _ | _, _ :: _, _, _, _, _ ->
          unsupported at "An or-pattern reading a mutable field"
      | _ -> unsupported at "An or-pattern binding variables"
    end
  | _ -> unsupported at "This pattern"

(** The cases of a match on the value [v], with the value of the matching one assigned to
    [target] if there is one; [total] if OCaml found them exhaustive. *)
and match_cases ?commits ~tail ctx ~at v
    (cases : (Typedtree.pattern * Typedtree.expression) list) ~total target =
  let l = loc at in
  let enclosing_names = ctx.procedure.names.scope in
  (* Each case starts in the state of the atomic update before the match. *)
  let start = au_snapshot ctx in
  let ends = ref [] in
  let snapshot_ends = ref [] in
  let start_positions = ctx.procedure.positions in
  let join = new_join () in
  let position_ends = ref [] in
  let commits =
    match commits with
    | Some commits -> commits
    | None -> List.map cases ~f:(fun _ -> None)
  in
  (* Whether each case linearizes the function, if the scrutinee is the value of a read
     that left the atomic update open, by the case's body. *)
  let case_commits = List.zip_exn (List.map cases ~f:snd) commits in
  (* The body of a case, after defining the variables of its pattern. *)
  let case_body ?(names = enclosing_names) binds (rhs : Typedtree.expression) =
    ctx.procedure.names.scope <- names;
    restore_au ctx start;
    let commits =
      Option.join
        (List.Assoc.find case_commits rhs ~equal:(fun a b ->
             Poly.equal a.exp_loc b.exp_loc))
    in
    let* entry = enter_arm ctx ~commits in
    let* defs =
      all binds ~f:(fun (id, value, t) ->
          let* typ = typ ctx ~at t in
          let x = Names.bind ~typ:t ctx.procedure.names id in
          Ok
            (R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs value) (ident ~loc:l x)
            @ assume_in_range ~loc:l t x))
    in
    let* stmts, value = expr ~tail ctx rhs in
    let* finish = finish_arm ctx ~tail value in
    let assignment =
      Option.value_map target ~default:[] ~f:(fun t -> [ assign t value ])
    in
    ends := au_state ctx :: !ends;
    snapshot_ends := ctx.procedure.snapshots :: !snapshot_ends;
    position_ends := ctx.procedure.positions :: !position_ends;
    let assigned = end_arm ctx join ~start:start_positions in
    Ok (entry @ List.concat defs @ stmts @ finish @ assignment @ assigned)
  in
  let not_exhaustive () =
    [ check ctx ~at "This match may not be exhaustive" (R.Expr.bool ~loc:l false) ]
  in
  let* stmts =
    match flat_cases ctx v cases with
    | Some flat ->
        let* raven_cases =
          all flat ~f:(fun (case, binds, in_range, rhs, names) ->
              let* body = case_body ~names binds rhs in
              Ok (case, in_range @ body))
        in
        let has_default =
          List.exists flat ~f:(fun (case, _, _, _, _) ->
              match case with R.Expr.Default -> true | Case _ -> false)
        in
        let default =
          if total || has_default then [] else [ (R.Expr.Default, not_exhaustive ()) ]
        in
        Ok [ R.Stmt.match_ ~loc:l v (raven_cases @ default) ]
    | None ->
        let rec chain = function
          | [] -> Ok (if total then [] else not_exhaustive ())
          | [ (p, rhs) ] when total ->
              let* access, _, binds = pattern ctx p v in
              let* body = case_body binds rhs in
              Ok (access @ body)
          | (p, rhs) :: rest -> begin
              let* access, cond, binds = pattern ctx p v in
              let* body = case_body binds rhs in
              match cond with
              | None -> Ok (access @ body)
              | Some cond ->
                  let* rest = chain rest in
                  Ok (access @ [ R.Stmt.if_ ~loc:l cond body rest ])
            end
        in
        chain cases
  in
  set_au_state ctx
    (Option.first_some
       (List.reduce (List.filter_opt !ends) ~f:join_au)
       (Option.map
          (let au, _, _ = start in
           au)
          ~f:(fun (state, _, _, _) -> state)));
  ctx.procedure.snapshots <- common_snapshots !snapshot_ends;
  ctx.procedure.positions <- join_positions join ~start:start_positions !position_ends;
  Ok (join.decls @ stmts)

(** The cases of a Raven match on [v] for [cases], if their patterns are flat: distinct
    constructors with variables or [_] as arguments, possibly followed by a variable or
    [_] matching anything else. *)
and flat_cases ctx v cases =
  let enclosing_names = ctx.procedure.names.scope in
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
              ( Datatypes.find_cstr ctx.given.types cstr,
                Option.all (List.map ps ~f:flat_arg) )
            with
            | Some (_, c), Some args when not (List.mem seen c.raven ~equal:String.equal)
              ->
                Option.map
                  (flat (c.raven :: seen) rest)
                  ~f:(fun rest -> (`Ctor (c, args, p), rhs) :: rest)
            | _ -> None
            end
        | _ -> None
        end
  in
  let case item =
    ctx.procedure.names.scope <- enclosing_names;
    match item with
    | `Any (id, (p : Typedtree.pattern)), rhs ->
        let binds =
          Option.value_map id ~default:[] ~f:(fun id -> [ (id, v, p.pat_type) ])
        in
        (R.Expr.Default, binds, [], rhs, ctx.procedure.names.scope)
    | `Ctor ((c : Datatypes.ctor), args, (p : Typedtree.pattern)), rhs ->
        let l = loc p.pat_loc in
        let var = function
          | None -> (ident ~loc:l "_", [])
          | Some (id, t) ->
              let x = Names.bind ~typ:t ctx.procedure.names id in
              (ident ~loc:l x, assume_in_range ~loc:l t x)
        in
        let vars = List.map args ~f:var in
        ( R.Expr.Case (ident ~loc:l c.raven, List.map vars ~f:fst),
          [],
          List.concat_map vars ~f:snd,
          rhs,
          ctx.procedure.names.scope )
  in
  let result = Option.map (flat [] cases) ~f:(List.map ~f:case) in
  ctx.procedure.names.scope <- enclosing_names;
  result

(** [if c then e1 else e2], with its value assigned to [target] if there is one. *)
and conditional ctx ~at ?polarity ~tail c (e1 : Typedtree.expression)
    (e2 : Typedtree.expression option) target =
  let l = loc at in
  (* Each arm starts in the state of the atomic update before the branch; if [c] is the
     result of the [compare_and_set] that left the update open, the arms close it. *)
  let start = au_snapshot ctx in
  let start_positions = ctx.procedure.positions in
  let join = new_join () in
  let arm taken e =
    restore_au ctx start;
    let* entry =
      enter_arm ctx ~commits:(Option.map polarity ~f:(fun p -> Bool.equal p taken))
    in
    let* stmts =
      match e with
      | None -> finish_arm ctx ~tail (unit_value ~loc:l)
      | Some e ->
          let* stmts, v = expr ~tail ctx e in
          let* finish = finish_arm ctx ~tail v in
          let assignment =
            Option.value_map target ~default:[] ~f:(fun t -> [ assign t v ])
          in
          Ok (stmts @ finish @ assignment)
    in
    let assigned = end_arm ctx join ~start:start_positions in
    Ok
      ( entry @ stmts @ assigned,
        (au_state ctx, ctx.procedure.snapshots, ctx.procedure.positions) )
  in
  let* then_, (then_state, then_snapshots, then_positions) = arm true (Some e1) in
  let* else_, (else_state, else_snapshots, else_positions) = arm false e2 in
  set_au_state ctx (Option.map2 then_state else_state ~f:join_au);
  ctx.procedure.snapshots <- common_snapshots [ then_snapshots; else_snapshots ];
  ctx.procedure.positions <-
    join_positions join ~start:start_positions [ then_positions; else_positions ];
  Ok (join.decls @ [ R.Stmt.if_ ~loc:l c then_ else_ ])

(** The statements [make target] computing the value of [e] into a new variable [target],
    and that variable; no variable if [e] is of type unit. *)
and branch ctx (e : Typedtree.expression) make =
  let l = loc e.exp_loc in
  if is_unit e.exp_type then
    let* stmts = make None in
    Ok (stmts, unit_value ~loc:l)
  else
    let* typ = typ ctx ~at:e.exp_loc e.exp_type in
    let x = Names.fresh ctx.procedure.names "tmp" in
    let* stmts = make (Some (x, l)) in
    Ok
      ( R.Stmt.local ~loc:l ~const:false ~typ (ident ~loc:l x) @ stmts,
        R.Expr.var ~loc:l (name ~loc:l x) )

and assign (x, l) v =
  R.Stmt.assign ~loc:l [ R.Expr.var ~loc:l (name ~loc:l x) ] (R.Stmt.expr_rhs v)

(** The pure expression [e] as a Raven expression, with the values of its let-bound
    variables in [values]; [funcs] are the functions it may call, by their OCaml compiler
    paths, with their Raven names. *)
and pure ?(reads = []) ctx ~funcs (values : (string * R.Expr.t) list)
    (e : Typedtree.expression) : (R.Expr.t, error) Result.t =
  let at = e.exp_loc in
  let l = loc at in
  let pure_in values = pure ~reads ctx ~funcs values in
  let not_pure what =
    unsupported at (what ^ " in a function that contracts use, which must be pure,")
  in
  match e.exp_desc with
  | Texp_ident (Pident id, _, _) ->
      begin match
        ( List.Assoc.find values (Ident.unique_name id) ~equal:String.equal,
          Names.find ctx.procedure.names id )
      with
      | Some v, _ -> Ok v
      | None, Some x -> Ok (R.Expr.var ~loc:l (name ~loc:l x))
      | None, None -> not_pure "A function used as a value"
      end
  | Texp_ident (p, _, _) ->
      begin match stdlib_name p with
      | Some "max_int" -> Ok (R.Expr.int ~loc:l Prelude.max_int)
      | Some "min_int" -> Ok (R.Expr.int ~loc:l Prelude.min_int)
      | _ -> not_pure "This identifier"
      end
  | Texp_constant (Const_int n) -> Ok (R.Expr.int ~loc:l n)
  | Texp_construct ({ txt = Lident (("true" | "false") as b); _ }, _, []) ->
      Ok (R.Expr.bool ~loc:l (String.equal b "true"))
  | Texp_construct ({ txt = Lident "()"; _ }, _, []) -> Ok (unit_value ~loc:l)
  | Texp_construct (_, cstr, args) ->
      begin match Datatypes.find_cstr ctx.given.types cstr with
      | None -> not_pure "This constructor"
      | Some (d, c) ->
          let* args = all args ~f:(pure_in values) in
          Ok (R.Expr.call ~loc:l (Datatypes.ctor_name ~loc:l d c) args)
      end
  | Texp_tuple components ->
      let* components = all components ~f:(fun (_, c) -> pure_in values c) in
      Ok (R.Expr.tuple ~loc:l components)
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, _); _ },
        [ (Nolabel, Arg ({ exp_desc = Texp_ident (Pident r, _, _); _ } as cell)) ] )
    when Option.equal String.equal (stdlib_name path) (Some "!") ->
      begin match
        (Names.find ctx.procedure.names r, Datatypes.desc ctx.given.types cell.exp_type)
      with
      | Some x, Tconstr (_, [ elt ], _) -> begin
          let* field = ref_field ctx ~at elt in
          match List.Assoc.find reads (x, field) ~equal:Poly.equal with
          | Some v -> Ok v
          | None -> not_pure "A read of a reference"
        end
      | _ -> not_pure "A read of a reference"
      end
  | Texp_field ({ exp_desc = Texp_ident (Pident r, _, _); _ }, _, label)
    when Option.is_some (Names.find ctx.procedure.names r) -> begin
      let* field = field_of_label ctx ~at label in
      let x = Option.value_exn (Names.find ctx.procedure.names r) in
      match field with
      | Some (field, true) ->
          begin match List.Assoc.find reads (x, field) ~equal:Poly.equal with
          | Some v -> Ok v
          | None -> not_pure "A read of a reference"
          end
      | Some (field, false) ->
          Ok
            (R.Expr.field ~loc:l
               (R.Expr.var ~loc:l (name ~loc:l x))
               (qualified_name ~loc:l field))
      | None -> not_pure "This field"
    end
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, [ (_, Arg a); (_, Arg b) ])
    when runtime_structural_equality_unsafe ctx path a b ->
      error at "Structural equality on values containing references is unsupported"
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, [ (_, Arg a); (_, Arg b) ])
    when is_physical path && not (exact_physical ctx.given.types a b) ->
      not_pure "Physical equality on values that are not immediate"
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, args) -> begin
      let* args = plain_args ~at args in
      let* args = all args ~f:(pure_in values) in
      match (binop_of_path path, unop_of_path path, path, args) with
      | Some Div, _, _, [ a; b ] -> Ok (prelude_call ~loc:l Prelude.div [ a; b ])
      | Some Mod, _, _, [ a; b ] -> Ok (prelude_call ~loc:l Prelude.mod_ [ a; b ])
      | Some op, _, _, [ a; b ] -> Ok (R.Expr.binary ~loc:l op a b)
      | _, Some `Not, _, [ a ] -> Ok (R.Expr.not_ ~loc:l a)
      | _, Some `Neg, _, [ a ] -> Ok (R.Expr.neg ~loc:l a)
      | None, None, path, _ ->
          let* path = Source.normalize_value_path e.exp_env ~at path in
          begin match Path_bindings.find funcs path with
          | Some f -> Ok (R.Expr.call ~loc:l (qualified_name ~loc:l f) args)
          | None -> not_pure ("A call of " ^ Path.name path)
          end
      | _ -> not_pure "This application"
    end
  | Texp_ifthenelse (c, a, Some b) ->
      let* c = pure_in values c in
      let* a = pure_in values a in
      let* b = pure_in values b in
      Ok (R.Expr.ite ~loc:l c a b)
  | Texp_let
      ( Nonrecursive,
        [ { vb_pat = { pat_desc = Tpat_var (id, _, _); _ }; vb_expr; _ } ],
        body ) ->
      let* v = pure_in values vb_expr in
      pure_in ((Ident.unique_name id, v) :: values) body
  | Texp_match (scrutinee, cases, [], Total) -> begin
      let* v = pure_in values scrutinee in
      let* cases =
        all cases ~f:(fun (c : Typedtree.computation Typedtree.case) ->
            match (Typedtree.split_pattern c.c_lhs, c.c_guard) with
            | (Some p, None), None -> Ok (p, c.c_rhs)
            | _ -> not_pure "A guard or an exception case")
      in
      let with_binds binds =
        List.fold binds ~init:values ~f:(fun values (id, value, _) ->
            (Ident.unique_name id, value) :: values)
      in
      match flat_cases ctx v cases with
      | Some flat ->
          let* cases =
            all flat ~f:(fun (case, binds, _, rhs, _) ->
                let* body = pure_in (with_binds binds) rhs in
                Ok (case, body))
          in
          Ok (R.Expr.match_ ~loc:l v cases)
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
                  | None -> Ok body
                  | Some cond ->
                      let* rest = chain rest in
                      Ok (R.Expr.ite ~loc:l cond body rest)
              end
          in
          chain cases
    end
  | Texp_match (_, _, _, Partial) -> not_pure "A match that may not be exhaustive"
  | _ -> not_pure "This expression"
