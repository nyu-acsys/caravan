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

(** Retains the receiver of destructured fields for implicit argument inference. *)
let rec record_projection_bindings (pattern : Typedtree.pattern) receiver =
  match pattern.pat_desc with
  | Tpat_alias (pattern, _, _, _, _) -> record_projection_bindings pattern receiver
  | Tpat_record (fields, _) ->
      State.iter fields ~f:(fun (_, label, pattern) ->
          match pattern.pat_desc with
          | Tpat_var (id, _, _) ->
              let* name = State.find_name id in
              begin match name with
              | Some name ->
                  State.modify_carried (fun carried ->
                      {
                        carried with
                        fields_of =
                          (name, (label.lbl_name, receiver)) :: carried.fields_of;
                      })
              | None -> State.return ()
              end
          | _ -> State.return ())
  | _ -> State.return ()

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

let cleared_source (expression : Typedtree.expression) =
  match expression.exp_desc with
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, declaration); _ },
        [ (Nolabel, Arg { exp_desc = Texp_construct (_, constructor, []); _ }) ] ) ->
      State.return
        (String.equal constructor.cstr_name "()" && unit_clear_cast path declaration)
  | Texp_ident (Pident id, _, _) -> State.cleared_binding id
  | _ -> State.return false

let clearing_annotation ctx (expression : Typedtree.expression) =
  if
    List.Assoc.mem ctx.given.access_proofs (Domain_calls.key expression) ~equal:Poly.equal
  then
    State.of_result
      (unsupported expression.exp_loc "An access proof attached to a clearing constant")
  else State.return ()

let cleared_value ctx (expression : Typedtree.expression) =
  let* () = clearing_annotation ctx expression in
  let at = expression.exp_loc in
  let l = loc at in
  let* raw_type = State.raw_type ctx.given ~at expression.exp_type in
  let raw =
    R.Expr.annotated
      (R.Expr.call ~loc:l (qualified_name ~loc:l "Option.none") [])
      raw_type
  in
  let* typ = State.typ ctx ~at expression.exp_type in
  let* x = State.fresh "discarded_payload" in
  let value = R.Expr.var ~loc:l (name ~loc:l x) in
  let+ () = State.register_raw value raw in
  ( R.Stmt.local ~loc:l ~typ
      ~init:(R.Stmt.expr_rhs (State.raw_project ~loc:l raw))
      (ident ~loc:l x),
    value )

(** The statements evaluating [e], and the value of [e] after them; [tail] if the value is
    the function's result. *)
let rec expr ?(tail = false) ?(continue_state = false) ?(keep_scope = false)
    ?(allow_raw = false) (ctx : context) (e : Typedtree.expression) :
    (R.Stmt.t list * R.Expr.t) State.t =
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
  let allow_raw = allow_raw || (tail && ctx.given.raw_return) in
  let* statements, value =
    expr_body ~tail ~keep_scope ~raw:(allow_raw && ctx.given.raw_flow) ctx e
  in
  let* finish =
    match adapter with
    | None -> State.return []
    | Some a -> return_proof ctx a ~result_type:e.exp_type ~result:value
  in
  let* checked =
    if allow_raw then State.return [] else State.check_raw ~at:e.exp_loc value
  in
  let* stateful = State.of_result (stateful_access ctx.given.access_proofs e) in
  let* () =
    if not (continue_state && stateful) then
      State.modify_carried (fun c -> { c with proof_state = incoming })
    else State.return ()
  in
  let* () = if not keep_scope then State.set_scope incoming_names else State.return () in
  let+ () = State.modify_carried (fun c -> { c with return_covered = covered }) in
  (statements @ finish @ checked, value)

and expr_body ~tail ~keep_scope ~raw (ctx : context) (e : Typedtree.expression) :
    (R.Stmt.t list * R.Expr.t) State.t =
  let at = e.exp_loc in
  let l = loc at in
  match e.exp_desc with
  | Texp_struct_item
      ({ str_desc = Tstr_open { open_expr = { mod_desc = Tmod_ident _; _ }; _ }; _ }, body)
    ->
      expr ~tail ~keep_scope ~allow_raw:raw ctx body
  | Texp_ident (Pident id, _, _) ->
      let* cleared = State.cleared_binding id in
      if cleared then cleared_value ctx e
      else begin
        let* x = State.find_name id in
        match x with
        | Some x -> State.return ([], R.Expr.var ~loc:l (name ~loc:l x))
        | None -> State.of_result (unsupported at "A function used as a value")
      end
  | Texp_ident (path, _, declaration) -> (
      let* path = State.of_result (Source.normalize_value_path e.exp_env ~at path) in
      match Path_bindings.find ctx.given.libraries path with
      | Some member ->
          let* () =
            State.of_result
              (match Datatypes.desc ctx.given.types e.exp_type with
              | Tarrow _ -> unsupported at "An imported function used as a value"
              | _ -> Ok ())
          in
          let* target =
            State.polymorphic_call ~environment:e.exp_env ctx ~at ~path
              ~declaration:declaration.val_type ~occurrence:e.exp_type
              ~target:(String.concat ~sep:"." member)
          in
          let value = R.Expr.call ~loc:l (qualified_name ~loc:l target) [] in
          if Path_bindings.mem ctx.given.contracted_values path then
            let call =
              R.Expr.call ~loc:l
                (qualified_name ~loc:l (library_value_accessor target))
                [ value ]
            in
            State.return ([ R.Stmt.call ~loc:l call ], value)
          else State.return ([], value)
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
      let+ commit = unit_linearization ctx e in
      (commit, unit_value ~loc:l)
  | Texp_construct (_, cstr, args) ->
      begin match
        occurrence_constructor ~environment:e.exp_env ctx.given.types e.exp_type cstr
      with
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
      let+ stmts, components =
        operands ~continue_state:true ctx (List.map components ~f:snd)
      in
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
      let* evaluated =
        State.all (List.rev values) ~f:(fun (label, value) ->
            let* field =
              State.field_of_label ctx.given ~at ~record_type:e.exp_type label
            in
            let* raw =
              match field with
              | Some (field, true) -> State.raw_storage field
              | _ -> State.return false
            in
            expr ~continue_state:true ~allow_raw:raw ctx value)
      in
      let stmts = List.concat_map evaluated ~f:fst in
      let args = List.rev_map evaluated ~f:snd in
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
                let+ field =
                  State.field_of_label ctx.given ~at ~record_type:e.exp_type label
                in
                fst (Option.value_exn field))
          in
          let checkpoint =
            let* owner = State.owner ctx.given ~at in
            let+ stamp = State.fresh "write_event" in
            let event = R.Expr.var ~loc:l (name ~loc:l stamp) in
            let preparation =
              R.Stmt.local ~loc:l ~ghost:true ~typ:(R.Type.ref ~loc:l)
                ~init:
                  (R.Stmt.expr_rhs
                     (Visibility_contract.call ~loc:l
                        ~module_name:Execution_contract.module_name
                        "visibility_checkpoint" [ owner ]))
                (ident ~loc:l stamp)
            in
            (owner, event, preparation)
          in
          let* initializers =
            State.all
              (List.zip_exn fields (List.zip_exn args values))
              ~f:(fun (field, (value, (_, expression))) ->
                let* relaxed = State.relaxed_storage ctx.given field in
                let* raw = State.raw_storage field in
                let* value =
                  if raw then
                    State.raw_inject ctx.given ~at ~elt:expression.exp_type value
                  else State.return value
                in
                let contents = (qualified_name ~loc:l field, Some value) in
                match relaxed with
                | Some family ->
                    let+ owner, event, preparation = checkpoint in
                    ( preparation,
                      contents
                      :: Relaxed_fields_contract.initial_fields ~loc:l ~family ~value
                           ~event ~owner,
                      Some (family, owner, value, event) )
                | None -> (
                    let* frozen = State.frozen_storage ctx.given field in
                    match frozen with
                    | None -> State.return ([], [ contents ], None)
                    | Some family ->
                        let+ owner, event, preparation = checkpoint in
                        ( preparation,
                          contents
                          :: Frozen_visibility_contract.initial_fields ~loc:l ~family
                               ~owner ~event,
                          None )))
          in
          let* x = State.fresh "tmp" in
          let* views, view_args = view_allocation ctx ~loc:l fields in
          let+ explicit = allocation_initializers ctx e in
          let init =
            R.Stmt.new_rhs
              (List.concat_map initializers ~f:(fun (_, fields, _) -> fields)
              @ view_args @ explicit)
          in
          let result = R.Expr.var ~loc:l (name ~loc:l x) in
          let initialize =
            List.filter_map initializers ~f:(fun (_, _, state) ->
                Option.map state ~f:(fun (family, owner, value, event) ->
                    R.Stmt.call ~loc:l
                      (R.Expr.call ~loc:l
                         (qualified_name ~loc:l (family ^ ".initialize"))
                         [ owner; result; value; event ])))
          in
          ( stmts
            @ List.concat_map initializers ~f:(fun (preparation, _, _) -> preparation)
            @ views
            @ R.Stmt.local ~loc:l ~typ ~init (ident ~loc:l x)
            @ initialize,
            result )
      | Some ({ ctors = [ c ]; _ } as d) ->
          let+ value = constructor_value ctx ~at ~result_type:e.exp_type d c args in
          (stmts, value)
      | _ -> State.of_result (unsupported at "This record")
      end
  | Texp_record _ -> State.of_result (unsupported at "A record copied with changes")
  | Texp_field (record, _, label) -> begin
      let* stmts, v = expr ctx record in
      let* field =
        State.field_of_label ctx.given ~at ~record_type:record.exp_type label
      in
      match field with
      | Some (field, true) ->
          let annotation =
            List.Assoc.find ctx.given.access_proofs (Domain_calls.key e) ~equal:Poly.equal
          in
          let* reading, value =
            match annotation with
            | None ->
                State.ordinary_read
                  ~immutable:(Poly.equal label.lbl_mut Immutable)
                  ctx.given ~at ~field ~elt:e.exp_type v
            | Some annotation ->
                let* () =
                  if ctx.given.manual then State.return ()
                  else
                    State.of_result
                      (error annotation.loc "Ghost.scope requires a manual function proof")
                in
                let* scope = State.of_result (Annotation.scope annotation) in
                access_proof ctx annotation ~result_type:e.exp_type
                  ~mode:
                    (if Poly.equal scope.scope_mode S.Published_scope then
                       S.Published_scope
                     else S.Frozen_scope)
                  (fun _ ->
                    let+ statements, value =
                      State.ordinary_read
                        ~immutable:(Poly.equal label.lbl_mut Immutable)
                        ~frozen:(Poly.equal scope.scope_mode S.Frozen_scope)
                        ~published:(Poly.equal scope.scope_mode S.Published_scope)
                        ctx.given ~at ~field ~elt:e.exp_type v
                    in
                    (statements, value, [], []))
          in
          State.return (stmts @ reading, value)
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
      let value_type = value.exp_type in
      let record_type = record.exp_type in
      let* resolved = State.field_of_label ctx.given ~at ~record_type label in
      let* raw =
        match resolved with
        | Some (field, true) -> State.raw_storage field
        | _ -> State.return false
      in
      let* value_stmts, value = expr ~allow_raw:raw ctx value in
      let* record_stmts, record = expr ctx record in
      let* field = State.field_of_label ctx.given ~at ~record_type label in
      match field with
      | Some (field, true) ->
          let+ writing, result =
            native_access ctx e (fun _ ->
                let+ writing =
                  State.ordinary_write ctx.given ~at ~field ~elt:value_type record value
                in
                (writing, unit_value ~loc:l, [], []))
          in
          (value_stmts @ record_stmts @ writing, result)
      | _ -> State.of_result (unsupported at "This field")
    end
  | Texp_match (_, cases, [], _)
    when tail && ctx.given.raw_return
         && List.exists cases ~f:(fun case ->
             Option.is_some (snd (Typedtree.split_pattern case.Typedtree.c_lhs))) ->
      State.of_result (unsupported at "Exception handling with a raw result")
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
          (Witnesses.arms ?universal:ctx.given.universal_result ctx.given.types ~at
             ~current:ctx.given.current_polymorphic ~scrutinee:scrutinee.exp_type
             ~result:e.exp_type cases)
      in
      let* () =
        if raw && Option.is_some arm then
          State.of_result (unsupported at "Witness result conversion with a raw join")
        else State.return ()
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
        branch ~raw ctx e (fun target ->
            match_cases ~raw ?commits ?arm ~tail ctx ~at v cases ~total target)
      in
      (scrutinee_stmts @ naming @ fst stmts, snd stmts)
  | Texp_match (_, _, _ :: _, _) -> State.of_result (unsupported at "An effect handler")
  | Texp_try _ when tail && ctx.given.raw_return ->
      State.of_result (unsupported at "Exception handling with a raw result")
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
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, declaration); _ },
        [ (Nolabel, Arg { exp_desc = Texp_construct (_, constructor, []); _ }) ] )
    when String.equal constructor.cstr_name "()" && unit_clear_cast path declaration ->
      cleared_value ctx e
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
      let* normalized =
        State.of_result (Source.normalize_value_path e.exp_env ~at path)
      in
      if stdlib_list_fold_left normalized then fold_left ctx e args
      else
        let* args = State.of_result (supplied_args ~at args) in
        apply ctx e path declaration callee.exp_type args
  | Texp_apply _ -> State.of_result (unsupported at "This application")
  | Texp_ifthenelse (c, e1, e2) ->
      let* polarity = cas_polarity c in
      let* c_stmts, c = expr ctx c in
      let+ stmts =
        branch ~raw ctx e (fun target ->
            conditional ~raw ctx ~at ?polarity ~tail c e1 e2 target)
      in
      (c_stmts @ fst stmts, snd stmts)
  | Texp_let (_, [ { vb_pat = { pat_desc = Tpat_var (id, _, _); _ }; _ } ], rest)
    when Path_bindings.mem ctx.given.functions (Path.Pident id) ->
      (* A local function, lifted to the top level. *)
      expr ~tail ~keep_scope ~allow_raw:raw ctx rest
  | Texp_let (Nonrecursive, bindings, body) ->
      (* The bound expressions are evaluated before any of their variables is bound. *)
      let* evaluated =
        State.all bindings ~f:(fun (vb : Typedtree.value_binding) ->
            let* clear = cleared_source vb.vb_expr in
            let generalized =
              clear
              && (match vb.vb_pat.pat_desc with Tpat_var _ -> true | _ -> false)
              && List.exists (Polymorphic_functions.all_variables vb.vb_expr.exp_type)
                   ~f:(fun typ ->
                     Option.is_none (Datatypes.find_variable ctx.given.types typ))
            in
            if generalized then
              let+ () = clearing_annotation ctx vb.vb_expr in
              (vb, [], unit_value ~loc:l, true)
            else
              let* polarity = cas_polarity vb.vb_expr in
              let* read = is_read_value vb.vb_expr in
              let* stmts, v =
                expr ~allow_raw:true
                  ~continue_state:(List.length bindings = 1)
                  ctx vb.vb_expr
              in
              let+ () =
                match (polarity, vb.vb_pat.pat_desc) with
                | Some p, Tpat_var (id, _, _) -> record_cas_result id p
                | None, Tpat_var (id, _, _) when read -> record_read_result id
                | _ -> State.return ()
              in
              (vb, stmts, v, false))
      in
      let* defs =
        State.all evaluated ~f:(fun ((vb : Typedtree.value_binding), _, v, generalized) ->
            if generalized then
              begin match vb.vb_pat.pat_desc with
              | Tpat_var (id, _, _) ->
                  let+ () = State.bind_cleared id in
                  []
              | _ ->
                  State.of_result
                    (unsupported vb.vb_pat.pat_loc "A generalized clearing pattern")
              end
            else
              let* reading, cond, binds = pattern ~allow_raw:true ctx vb.vb_pat v in
              match cond with
              | Some _ ->
                  State.of_result
                    (unsupported vb.vb_pat.pat_loc "A refutable pattern in a let binding")
              | None ->
                  let* defs =
                    State.all binds ~f:(fun (id, value, t) ->
                        let* typ = State.typ ctx ~at t in
                        let* () = State.note_domain ctx.given.types t in
                        let* x = State.bind_name ~typ:t id in
                        let* raw = State.raw_value value in
                        let+ () =
                          match raw with
                          | None -> State.return ()
                          | Some raw ->
                              State.register_raw (R.Expr.var ~loc:l (name ~loc:l x)) raw
                        in
                        R.Stmt.local ~loc:l ~const:true ~typ ~init:(R.Stmt.expr_rhs value)
                          (ident ~loc:l x)
                        @
                        if Option.is_some raw then []
                        else assert_admissible ctx ~loc:l t x)
                  in
                  let+ () = record_projection_bindings vb.vb_pat v in
                  reading @ List.concat defs)
      in
      let last = List.last_exn bindings in
      let* ghost =
        ghost ctx ~after:last.vb_expr.exp_loc.loc_end ~before:body.exp_loc.loc_start
      in
      let+ body_stmts, body = expr ~tail ~keep_scope ~allow_raw:raw ctx body in
      ( List.concat_map evaluated ~f:(fun (_, stmts, _, _) -> stmts)
        @ List.concat defs @ ghost @ body_stmts,
        body )
  | Texp_let (Recursive, _, _) ->
      State.of_result (unsupported at "A local recursive function")
  | Texp_sequence (e1, e2) ->
      let* stmts1, _ = expr ~continue_state:true ctx e1 in
      let* ghost = ghost ctx ~after:e1.exp_loc.loc_end ~before:e2.exp_loc.loc_start in
      let+ stmts2, v = expr ~tail ~keep_scope ~allow_raw:raw ctx e2 in
      (stmts1 @ ghost @ stmts2, v)
  | Texp_while (cond, body) ->
      let* () = no_loop_before_linearizing ~at in
      let* spec, annotation = State.of_result (loop_spec ctx ~after:cond.exp_loc body) in
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
      let* invariants = loop_invariants ?guard ?annotation ctx ~at spec ~relation in
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
      let* spec, annotation = State.of_result (loop_spec ctx ~after:hi.exp_loc body) in
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
        loop_invariants ~counter:i ?guard ?annotation ctx ~at spec ~relation:(fun _ ->
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
  let* normalized =
    State.of_result (Source.normalize_value_path e.exp_env ~at:e.exp_loc path)
  in
  match Mutex_primitives.operation normalized with
  | Some operation -> mutex_call ctx e operation args
  | None ->
      begin match Condition_primitives.operation normalized with
      | Some operation -> condition_call ctx e operation args
      | None ->
          begin match
            List.Assoc.find ctx.given.domain_calls (Domain_calls.key e) ~equal:Poly.equal
          with
          | Some domain -> domain_call ctx e domain
          | None -> apply_ordinary ctx e path declaration occurrence args
          end
      end

and native_access ctx (e : Typedtree.expression) run =
  match
    List.Assoc.find ctx.given.access_proofs (Domain_calls.key e) ~equal:Poly.equal
  with
  | None ->
      let+ statements, value, _, _ = run None in
      (statements, value)
  | Some annotation ->
      access_proof ctx annotation ~result_type:e.exp_type ~input_types:[] ~output_types:[]
        (fun values -> run (Some values))

and mutex_call ctx (e : Typedtree.expression) operation args =
  let at = e.exp_loc in
  let l = loc at in
  match (operation, args) with
  | Mutex_primitives.Create, [ argument ] ->
      let* statements, _ = expr ctx argument in
      let* () = State.note_mutex_support in
      let run _ =
        let+ result = State.fresh "mutex" in
        let value = R.Expr.var ~loc:l (name ~loc:l result) in
        ( R.Stmt.local ~loc:l ~typ:(R.Type.ref ~loc:l)
            ~init:
              (R.Stmt.expr_rhs
                 (match ctx.given.execution_owner with
                 | None -> Mutex_contract.create ~loc:l
                 | Some owner when ctx.given.mutex_execution ->
                     Mutex_contract.create_in_execution ~loc:l owner
                 | Some _ -> Mutex_contract.create ~loc:l))
            (ident ~loc:l result),
          value,
          [],
          [] )
      in
      let* creation, value = native_access ctx e run in
      State.return (statements @ creation, value)
  | Create, _ -> State.of_result (unsupported at "This Mutex.create application")
  | (Lock | Unlock | Try_lock), [ mutex ] when ctx.given.mutex_execution ->
      let receivers =
        List.filter_map args ~f:(fun argument ->
            match argument.Typedtree.exp_desc with
            | Texp_field (record, _, _) -> Some record.exp_type
            | _ -> None)
      in
      let* facade = Mutex_execution.native_protocol ctx ~at ~receivers in
      let* owner =
        State.of_result
          (Report.expect ~at "The native execution owner" ctx.given.execution_owner)
      in
      let* statements, mutex = expr ctx mutex in
      let run _ =
        match operation with
        | Lock ->
            State.return
              ( [ R.Stmt.call ~loc:l (Mutex_contract.lock ~loc:l ~facade mutex owner) ],
                unit_value ~loc:l,
                [],
                [] )
        | Unlock ->
            State.return
              ( [ R.Stmt.call ~loc:l (Mutex_contract.unlock ~loc:l ~facade mutex owner) ],
                unit_value ~loc:l,
                [],
                [] )
        | Try_lock ->
            let+ result = State.fresh "locked" in
            ( R.Stmt.local ~loc:l ~typ:(R.Type.bool ~loc:l)
                ~init:
                  (R.Stmt.expr_rhs (Mutex_contract.try_lock ~loc:l ~facade mutex owner))
                (ident ~loc:l result),
              R.Expr.var ~loc:l (name ~loc:l result),
              [],
              [] )
        | Create | Protect -> State.of_result (error at "Invalid native Mutex access")
      in
      let* access, value = native_access ctx e run in
      State.return (statements @ access, value)
  | (Lock | Unlock | Try_lock), _ ->
      State.of_result (error at "Native Mutex access requires a Ghost.Mutex facade")
  | Protect, _ -> State.of_result (unsupported at "Mutex.protect")

and condition_call ctx (e : Typedtree.expression) operation args =
  let at = e.exp_loc in
  let l = loc at in
  match (operation, args) with
  | Condition_primitives.Create, [ argument ] ->
      let* statements, _ = expr ctx argument in
      let* () = State.note_condition_support in
      let run _ =
        let+ result = State.fresh "condition" in
        ( R.Stmt.local ~loc:l
            ~typ:(Condition_contract.typ ~loc:l)
            ~init:(R.Stmt.expr_rhs (Condition_contract.create ~loc:l))
            (ident ~loc:l result),
          R.Expr.var ~loc:l (name ~loc:l result),
          [],
          [] )
      in
      let+ creation, value = native_access ctx e run in
      (statements @ creation, value)
  | (Wait | Signal | Broadcast), _ when ctx.given.mutex_execution ->
      let* () =
        State.of_result
          (match (operation, args) with
          | Wait, [ _; _ ] | (Signal | Broadcast), [ _ ] -> Ok ()
          | _ -> unsupported at "This Condition application")
      in
      let receivers =
        List.filter_map args ~f:(fun argument ->
            match argument.Typedtree.exp_desc with
            | Texp_field (record, _, _) -> Some record.exp_type
            | _ -> None)
      in
      let* facade = Mutex_execution.native_protocol ctx ~at ~receivers in
      let* owner =
        State.of_result
          (Report.expect ~at "The native execution owner" ctx.given.execution_owner)
      in
      let* statements, arguments = operands ctx args in
      let method_ =
        match operation with
        | Wait -> "wait"
        | Signal -> "signal"
        | Broadcast -> "broadcast"
        | Create -> "create"
      in
      let run _ =
        State.return
          ( [
              R.Stmt.call ~loc:l
                (Mutex_contract.protocol_call ~loc:l ~facade method_
                   (arguments @ [ owner ]));
            ],
            unit_value ~loc:l,
            [],
            [] )
      in
      let+ access, value = native_access ctx e run in
      (statements @ access, value)
  | Create, _ -> State.of_result (unsupported at "This Condition.create application")
  | (Wait | Signal | Broadcast), _ ->
      State.of_result (error at "Native Condition access requires a Ghost.Mutex facade")

and domain_call ctx (e : Typedtree.expression) domain =
  let at = e.exp_loc in
  let l = loc at in
  let annotation =
    List.Assoc.find ctx.given.access_proofs (Domain_calls.key e) ~equal:Poly.equal
  in
  let scoped ~inputs ~outputs run =
    match annotation with
    | None ->
        let+ statements, value, _, after_call = run None in
        (statements @ after_call, value)
    | Some annotation ->
        access_proof ctx annotation ~result_type:e.exp_type ~input_types:inputs
          ~output_types:outputs (fun values -> run (Some values))
  in
  let instantiate task =
    let* instance =
      if List.is_empty task.domain_worker.variables then
        State.return task.domain_worker.name
      else
        State.value_instance ctx ~at ~target:task.domain_worker.name
          ~arguments:task.domain_arguments
    in
    let* () = State.note_call ctx.given instance in
    State.return
      {
        task with
        domain_runtime =
          Qualified_name.of_string (instance ^ "." ^ task.domain_runtime.name);
        domain_contract =
          Qualified_name.of_string (instance ^ "." ^ task.domain_contract.name);
      }
  in
  let member task method_ =
    Qualified_name.raven ~loc:l (Domain_contract.member_name task.domain_contract method_)
  in
  match domain with
  | Domain_fork (task, arguments) ->
      let* task = instantiate task in
      let ocaml_args =
        List.map arguments ~f:(function
          | Unit_argument -> None
          | Value_argument e -> Some e)
      in
      let* evaluated =
        State.all arguments ~f:(function
          | Unit_argument -> State.return ([], unit_value ~loc:l)
          | Value_argument expression -> expr ctx expression)
      in
      let values = List.map evaluated ~f:snd in
      let run explicit =
        let* ghosts =
          Call_witnesses.infer_ghost_inputs ctx ~at ~callee:task.domain_procedure
            ~ocaml_args ~prefix_count:0 ~explicit
        in
        let* history =
          Call_witnesses.history_inputs ctx ~at ~callee:task.domain_procedure
            ~argument_types:task.domain_inputs ~prefix_count:0 ~args:(values @ ghosts)
        in
        let* handle_name = State.fresh "domain" in
        let* child_statements, child_arguments =
          let execution = execution_profile ctx.given in
          if not (Execution_contract.enabled execution) then State.return ([], [])
          else
            let* initialization, parents =
              if ctx.given.visibility_execution then
                let+ parent = State.owner ctx.given ~at in
                (Execution_contract.start_child ~loc:l parent, [ parent ])
              else State.return (Execution_contract.start ~loc:l, [])
            in
            let+ child = State.fresh "domain_child" in
            ( R.Stmt.local ~loc:l ~ghost:true ~typ:(R.Type.ref ~loc:l)
                ~init:(R.Stmt.expr_rhs initialization)
                (ident ~loc:l child),
              Execution_contract.captured_values execution
                (R.Expr.var ~loc:l (name ~loc:l child))
              @ parents )
        in
        let adapter =
          { task.domain_runtime with name = "fork$" ^ task.domain_template }
        in
        State.return
          ( child_statements
            @ R.Stmt.local ~loc:l ~typ:(R.Type.ref ~loc:l)
                ~init:
                  (R.Stmt.expr_rhs
                     (R.Expr.call ~loc:l
                        (Qualified_name.raven ~loc:l adapter)
                        (values @ ghosts @ history @ child_arguments)))
                (ident ~loc:l handle_name),
            R.Expr.var ~loc:l (name ~loc:l handle_name),
            [],
            [] )
      in
      let+ statements, value =
        scoped ~inputs:(List.map task.domain_ghost_inputs ~f:snd) ~outputs:[] run
      in
      (List.concat_map evaluated ~f:fst @ statements, value)
  | Domain_join (task, expression) ->
      let* task = instantiate task in
      let* statements, handle = expr ctx expression in
      let captures =
        Domain_contract.captures ~loc:l ~runtime:task.domain_runtime handle
      in
      let capture_count =
        List.length task.domain_inputs
        + List.length task.domain_ghost_inputs
        + List.length task.domain_implicit_inputs
        + (2 * task.domain_history_inputs)
        + List.length
            (Execution_contract.captured_types ~loc:l (execution_profile ctx.given))
      in
      let output_count =
        List.length task.domain_ghost_outputs + (2 * task.domain_history_outputs)
      in
      let projection value count index =
        if count = 1 then value else R.Expr.tuple_get ~loc:l value index
      in
      let raises = match task.domain_raises with State.Raises [] -> false | _ -> true in
      let* capture_outcome =
        match annotation with
        | Some annotation when raises ->
            State.of_result
              (access_captures_outcome annotation
                 ~outputs:(List.length task.domain_ghost_outputs))
        | _ -> State.return false
      in
      let run _ =
        let* result_type = State.typ ctx ~at task.domain_result in
        let* result_name = State.fresh "domain_result" in
        let result = R.Expr.var ~loc:l (name ~loc:l result_name) in
        let* ghosts_name = State.fresh "domain_ghosts" in
        let ghosts = R.Expr.var ~loc:l (name ~loc:l ghosts_name) in
        let ghosts_type = R.Type.named ~loc:l (member task "GhostResults") [] in
        let* outcome_type =
          if raises then State.typ ctx ~at Translate_context.outcome_type
          else State.return (R.Type.tuple ~loc:l [])
        in
        let* outcome_name = State.fresh "domain_outcome" in
        let outcome = R.Expr.var ~loc:l (name ~loc:l outcome_name) in
        let* (state : State.state) = State.get in
        let arguments =
          List.mapi task.domain_inputs ~f:(fun index _ ->
              let hint =
                Option.bind
                  (Option.join (List.nth task.domain_capture_hints index))
                  ~f:(State.name_in state.names)
              in
              Option.value_map hint ~default:(projection captures capture_count index)
                ~f:(fun hint -> R.Expr.var ~loc:l (name ~loc:l hint)))
        in
        let arguments =
          arguments
          @ List.mapi task.domain_ghost_inputs ~f:(fun index _ ->
              projection captures capture_count (List.length task.domain_inputs + index))
        in
        let* history_decls, history =
          Call_witnesses.history_outputs ctx ~at ~callee:task.domain_procedure
            ~argument_types:task.domain_inputs ~prefix_count:0
            ~result_type:task.domain_result ~args:arguments
        in
        let* propagation =
          if not raises then State.return []
          else
            let* handlers =
              State.gets (fun (state : State.state) -> state.carried.handlers)
            in
            let* () =
              match (ctx.au, handlers) with
              | Some _, [] ->
                  State.of_result
                    (unsupported at
                       "A Domain.join that may raise in a function with an atomic \
                        contract")
              | _ -> State.return ()
            in
            propagate ~at ~certain:false ~typ:outcome_type outcome task.domain_raises
        in
        let public =
          List.mapi task.domain_ghost_outputs ~f:(fun index _ ->
              projection ghosts output_count index)
        in
        let history_assign =
          List.mapi history ~f:(fun index target ->
              R.Stmt.assign ~loc:l [ target ]
                (R.Stmt.expr_rhs
                   (projection ghosts output_count (List.length public + index))))
        in
        let propagation, after_call =
          if capture_outcome then ([], propagation) else (propagation, [])
        in
        let* join, unfolding =
          if ctx.given.visibility_execution then
            let+ receiver = State.owner ctx.given ~at in
            let sibling prefix =
              Qualified_name.raven ~loc:l
                { task.domain_runtime with name = prefix ^ task.domain_template }
            in
            (R.Expr.call ~loc:l (sibling "join$") [ handle; captures; receiver ], [])
          else
            State.return
              ( Domain_contract.join ~loc:l ~runtime:task.domain_runtime handle captures,
                [
                  R.Stmt.unfold ~loc:l (member task "postcondition")
                    [ captures; result; ghosts; outcome ];
                ] )
        in
        State.return
          ( R.Stmt.local ~loc:l ~typ:result_type (ident ~loc:l result_name)
            @ R.Stmt.local ~loc:l ~ghost:true ~typ:ghosts_type (ident ~loc:l ghosts_name)
            @ R.Stmt.local ~loc:l ~typ:outcome_type (ident ~loc:l outcome_name)
            @ history_decls
            @ [ R.Stmt.assign ~loc:l [ result; ghosts; outcome ] (R.Stmt.expr_rhs join) ]
            @ unfolding @ history_assign @ propagation,
            (if is_unit e.exp_type then unit_value ~loc:l else result),
            (public @ if capture_outcome then [ outcome ] else []),
            after_call )
      in
      let+ body, value =
        scoped ~inputs:[]
          ~outputs:
            (List.map task.domain_ghost_outputs ~f:snd
            @ if capture_outcome then [ outcome_type ] else [])
          run
      in
      (statements @ body, value)

and apply_ordinary ctx (e : Typedtree.expression) (path : Path.t) declaration occurrence
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
  | Some "ignore", [ value ] ->
      let+ statements, _ = expr ctx value in
      (statements, unit_value ~loc:l)
  | Some "ref", [ v ] ->
      let* () = State.require_memory_encoding ctx.given ~at "reference initialization" in
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
      (v_stmts @ r_stmts @ writing, unit_value ~loc:l)
  | Some (("incr" | "decr") as op), [ r ] ->
      let* field = contents r in
      let* stmts, r = expr ctx r in
      let int_type = Predef.type_int in
      let* reading, v = read r field int_type in
      let binop : R.Expr.binop = if String.equal op "incr" then Plus else Minus in
      let v' = Prelude.runtime_binary ~loc:l binop v (R.Expr.int ~loc:l 1) in
      let+ writing = State.ordinary_write ctx.given ~at ~field ~elt:int_type r v' in
      (stmts @ reading @ writing, unit_value ~loc:l)
  | _ -> apply_operator ctx e path declaration occurrence args

(** The application of [Atomic.op] to [args], in [e]. *)
and atomic ctx (e : Typedtree.expression) op (args : Typedtree.expression list) =
  let at = e.exp_loc in
  let l = loc at in
  let visibility_arguments ~write arguments =
    if not ctx.given.visibility_execution then State.return ([], arguments)
    else
      match ctx.given.execution_owner with
      | None ->
          State.of_result (error at "This atomic operation needs an execution context")
      | Some owner ->
          if not write then State.return ([], owner :: arguments)
          else
            let* prior = State.fresh "caravan$atomic_prior" in
            let value = R.Expr.var ~loc:l (name ~loc:l prior) in
            State.return
              ( R.Stmt.local ~loc:l ~ghost:true
                  ~typ:(Visibility_contract.view_type ~loc:l)
                  ~init:
                    (R.Stmt.expr_rhs
                       (Visibility_contract.snapshot ~loc:l
                          ~module_name:Execution_contract.module_name owner))
                  (ident ~loc:l prior),
                owner :: value :: arguments )
  in
  let atomic_result ~typ ~init ~published target =
    if not (published && ctx.given.visibility_execution) then
      State.return (R.Stmt.local ~loc:l ~typ ~init (ident ~loc:l target))
    else
      let+ output = State.fresh "caravan$atomic_published" in
      R.Stmt.local ~loc:l ~typ (ident ~loc:l target)
      @ R.Stmt.local ~loc:l ~ghost:true
          ~typ:(Visibility_contract.view_type ~loc:l)
          (ident ~loc:l output)
      @ [
          R.Stmt.assign ~loc:l
            [
              R.Expr.var ~loc:l (name ~loc:l target);
              R.Expr.var ~loc:l (name ~loc:l output);
            ]
            init;
        ]
  in
  let element (t : Types.type_expr) =
    match Datatypes.desc ctx.given.types t with
    | Tconstr (_, [ elt ], _) -> State.return elt
    | _ -> State.of_result (unsupported at "This atomic")
  in
  (* How the step linearizes the function: as its annotation says, or by default. *)
  let* linearization_annotation = State.of_result (linearization ctx e) in
  let how default =
    match (linearization_annotation, default) with
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
  let result ?(default = `Commit) ?op ?step_arguments ~contents f atomic args =
    let* typ = State.typ ctx ~at e.exp_type in
    let* x = State.fresh "tmp" in
    let v = R.Expr.var ~loc:l (name ~loc:l x) in
    let* preparation, arguments = visibility_arguments ~write:true (atomic :: args) in
    let init = R.Stmt.expr_rhs (R.Expr.call ~loc:l (qualified_name ~loc:l f) arguments) in
    let* how = how default in
    let step =
      Option.map op ~f:(fun (op, field) ->
          (op, field, atomic, Option.value step_arguments ~default:args, v))
    in
    let* access = atomic_result ~typ ~init ~published:true x in
    let+ step =
      linearize ?step ~value:v ~access_type:e.exp_type ~contents ctx ~at how
        (preparation @ access)
    in
    (step, v)
  in
  let* elt =
    match args with
    | a :: _ when not (String.is_prefix op ~prefix:"make") -> element a.exp_type
    | _ -> element e.exp_type
  in
  let* field = State.atomic_field ctx.given ~at elt in
  let* visibility_family =
    if ctx.given.visibility_execution then
      State.map (State.visibility_atomic ctx.given ~at elt) ~f:Option.some
    else State.return None
  in
  let* nested =
    State.of_result (nested_stateful_atomic_argument ctx.given.access_proofs e)
  in
  let* stmts, values =
    match nested with
    | Some argument ->
        let+ stmts, value = expr ~continue_state:true ctx argument in
        (stmts, [ value ])
    | None -> operands ctx args
  in
  let primitive op = State.primitive ctx.given ~at elt op in
  let* publication =
    match
      List.Assoc.find ctx.given.access_proofs (Domain_calls.key e) ~equal:Poly.equal
    with
    | None -> State.return None
    | Some annotation ->
        let+ scope = State.of_result (Annotation.scope annotation) in
        if
          Poly.equal scope.scope_mode S.Release_scope
          || Poly.equal scope.scope_mode S.Acquire_scope
        then Some (annotation, scope.scope_mode)
        else None
  in
  match publication with
  | Some (annotation, mode) ->
      let* () =
        if ctx.given.manual then State.return ()
        else
          State.of_result
            (error annotation.loc "Publication scopes require a manual function proof")
      in
      let* () =
        if Option.is_none linearization_annotation then State.return ()
        else
          State.of_result
            (error annotation.loc
               "A publication scope cannot be combined with an automatic linearization \
                annotation")
      in
      let* family =
        State.of_result
          (Report.expect ~at "Visibility-aware atomics for a publication scope"
             visibility_family)
      in
      let* () =
        if String.is_prefix op ~prefix:"make" then
          let allocation =
            Datatypes.allocation_tag ~prefix:"atomic_" ~suffix:"" ctx.given.types elt
          in
          let* views, fields = view_allocation ctx ~loc:l (Option.to_list allocation) in
          let* explicit = allocation_initializers ctx e in
          if List.is_empty views && List.is_empty fields && List.is_empty explicit then
            State.return ()
          else
            State.of_result
              (unsupported at "Shared-mode atomic allocation with attached ghost fields")
        else State.return ()
      in
      let* owner = State.owner ctx.given ~at in
      let* view_type = State.of_result (visibility_view_type ctx.given ~at) in
      let* typ = State.typ ctx ~at e.exp_type in
      let run views =
        let* lower =
          match views with
          | [ view ] -> State.return view
          | _ ->
              State.of_result
                (error annotation.loc "A publication step takes one visibility view")
        in
        let prefix = [ owner; lower ] in
        let call method_ args =
          R.Stmt.expr_rhs
            (R.Expr.call ~loc:l
               (qualified_name ~loc:l (family ^ "." ^ method_))
               (prefix @ args))
        in
        match (mode, op, values) with
        | S.Acquire_scope, "get", [ address ] ->
            let+ x = State.fresh "tmp" in
            ( R.Stmt.local ~loc:l ~typ
                ~init:(call "get_acquire" [ address ])
                (ident ~loc:l x),
              R.Expr.var ~loc:l (name ~loc:l x),
              [],
              [] )
        | S.Acquire_scope, "compare_and_set", [ address; old_value; new_value ] ->
            let* x = State.fresh "tmp" in
            let+ statements =
              atomic_result ~typ
                ~init:
                  (call "compare_and_set_acquire"
                     [
                       address;
                       R.Expr.bool ~loc:l (Datatypes.immediate ctx.given.types elt);
                       old_value;
                       new_value;
                     ])
                ~published:true x
            in
            (statements, R.Expr.var ~loc:l (name ~loc:l x), [], [])
        | S.Release_scope, "set", [ address; value ] ->
            let+ published = State.fresh "caravan$atomic_published" in
            ( R.Stmt.local ~loc:l ~ghost:true
                ~typ:(Visibility_contract.view_type ~loc:l)
                ~init:(call "set" [ address; value ])
                (ident ~loc:l published),
              unit_value ~loc:l,
              [],
              [] )
        | S.Release_scope, ("fetch_and_add" | "incr" | "decr"), _ ->
            let* address, amount =
              match (op, values) with
              | "fetch_and_add", [ address; amount ] -> State.return (address, amount)
              | ("incr" | "decr"), [ address ] ->
                  State.return
                    (address, R.Expr.int ~loc:l (if String.equal op "incr" then 1 else -1))
              | _ -> State.of_result (error at "Invalid atomic publication operation")
            in
            let* target = primitive Fetch_and_add in
            let* x = State.fresh "tmp" in
            let+ statements =
              atomic_result ~typ:(R.Type.int ~loc:l)
                ~init:
                  (R.Stmt.expr_rhs
                     (R.Expr.call ~loc:l
                        (qualified_name ~loc:l target)
                        (prefix @ [ address; amount ])))
                ~published:true x
            in
            ( statements,
              (if String.equal op "fetch_and_add" then R.Expr.var ~loc:l (name ~loc:l x)
               else unit_value ~loc:l),
              [],
              [] )
        | S.Release_scope, ("make" | "make_contended" | "exchange" | "compare_and_set"), _
          ->
            let* method_, args =
              match (op, values) with
              | ("make" | "make_contended"), [ value ] -> State.return ("make", [ value ])
              | "exchange", [ address; value ] ->
                  State.return ("exchange", [ address; value ])
              | "compare_and_set", [ address; old_value; new_value ] ->
                  State.return
                    ( "compare_and_set",
                      [
                        address;
                        R.Expr.bool ~loc:l (Datatypes.immediate ctx.given.types elt);
                        old_value;
                        new_value;
                      ] )
              | _ -> State.of_result (error at "Invalid atomic publication operation")
            in
            let* x = State.fresh "tmp" in
            let+ statements =
              atomic_result ~typ ~init:(call method_ args) ~published:true x
            in
            (statements, R.Expr.var ~loc:l (name ~loc:l x), [], [])
        | _ ->
            State.of_result
              (error annotation.loc
                 "This publication scope does not match the atomic operation")
      in
      let* statements, value =
        access_proof ctx annotation ~mode ~result_type:e.exp_type
          ~input_types:[ view_type ] run
      in
      let+ () =
        match (op, values) with
        | "get", [ address ] -> record_read ctx ~atomic:address value
        | _ -> State.return ()
      in
      (stmts @ statements, value)
  | None ->
      begin match (op, values) with
      | ("make" | "make_contended"), [ v ] ->
          let allocation =
            Datatypes.allocation_tag ~prefix:"atomic_" ~suffix:"" ctx.given.types elt
          in
          let* x = State.fresh "tmp" in
          let* views, view_args =
            view_allocation ctx ~loc:l (Option.to_list allocation)
          in
          let* explicit = allocation_initializers ctx e in
          let* preparation, init =
            match visibility_family with
            | None ->
                State.return
                  ( [],
                    R.Stmt.new_rhs
                      ((qualified_name ~loc:l field, Some v) :: (view_args @ explicit)) )
            | Some family ->
                let* () =
                  if
                    List.is_empty views && List.is_empty view_args
                    && List.is_empty explicit
                  then State.return ()
                  else
                    State.of_result
                      (unsupported at
                         "Shared-mode atomic allocation with attached ghost fields")
                in
                let+ preparation, arguments = visibility_arguments ~write:true [ v ] in
                ( preparation,
                  R.Stmt.expr_rhs
                    (R.Expr.call ~loc:l
                       (qualified_name ~loc:l (family ^ ".make"))
                       arguments) )
          in
          let* () =
            if
              (not ctx.given.manual)
              && List.Assoc.mem ctx.given.access_proofs (Domain_calls.key e)
                   ~equal:Poly.equal
            then State.of_result (error at "Ghost.scope requires a manual function proof")
            else State.return ()
          in
          let* access = atomic_result ~typ:(R.Type.ref ~loc:l) ~init ~published:true x in
          let+ wrapped, value =
            native_access ctx e (fun _ ->
                State.return
                  (views @ preparation @ access, R.Expr.var ~loc:l (name ~loc:l x), [], []))
          in
          (stmts @ wrapped, value)
      | "get", [ a ] ->
          let* typ = State.typ ctx ~at e.exp_type in
          let* x = State.fresh "tmp" in
          let* preparation, read =
            match visibility_family with
            | None ->
                State.return
                  ( [],
                    R.Stmt.expr_rhs (R.Expr.field ~loc:l a (qualified_name ~loc:l field))
                  )
            | Some family ->
                let+ preparation, arguments = visibility_arguments ~write:false [ a ] in
                ( preparation,
                  R.Stmt.expr_rhs
                    (R.Expr.call ~loc:l
                       (qualified_name ~loc:l (family ^ ".get"))
                       arguments) )
          in
          let* how = how `Abort in
          let value = R.Expr.var ~loc:l (name ~loc:l x) in
          let* step =
            linearize ~value ~access_type:e.exp_type ~contents:elt ctx ~at how
              (preparation @ R.Stmt.local ~loc:l ~typ ~init:read (ident ~loc:l x))
          in
          let+ () = record_read ctx ~atomic:a value in
          (stmts @ step, R.Expr.var ~loc:l (name ~loc:l x))
      | "set", [ a; v ] ->
          let* how = how `Commit in
          let* access =
            match visibility_family with
            | None -> State.return [ write ~loc:l a field v ]
            | Some family ->
                let* preparation, arguments = visibility_arguments ~write:true [ a; v ] in
                let+ published = State.fresh "caravan$atomic_published" in
                preparation
                @ R.Stmt.local ~loc:l ~ghost:true
                    ~typ:(Visibility_contract.view_type ~loc:l)
                    ~init:
                      (R.Stmt.expr_rhs
                         (R.Expr.call ~loc:l
                            (qualified_name ~loc:l (family ^ ".set"))
                            arguments))
                    (ident ~loc:l published)
          in
          let+ step =
            linearize ~value:(unit_value ~loc:l) ~access_type:e.exp_type ~contents:elt ctx
              ~at how access
          in
          (stmts @ step, unit_value ~loc:l)
      | "exchange", [ a; v ] ->
          let* f = primitive Exchange in
          let+ reading, r = result ~contents:elt f a [ v ] in
          (stmts @ reading, r)
      | "compare_and_set", [ a; old_val; new_val ] ->
          let* f = primitive Compare_and_set in
          let arguments =
            if ctx.given.visibility_execution then
              [
                R.Expr.bool ~loc:l (Datatypes.immediate ctx.given.types elt);
                old_val;
                new_val;
              ]
            else [ old_val; new_val ]
          in
          let+ reading, r =
            result ~default:`Cas ~op:("compare_and_set", field)
              ~step_arguments:[ old_val; new_val ] ~contents:elt f a arguments
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
          let* preparation, arguments = visibility_arguments ~write:true [ a; n ] in
          let procedure =
            if ctx.given.visibility_execution then qualified_name ~loc:l f
            else name ~loc:l f
          in
          let init = R.Stmt.expr_rhs (R.Expr.call ~loc:l procedure arguments) in
          let* how = how `Commit in
          let* access = atomic_result ~typ:(R.Type.int ~loc:l) ~init ~published:true x in
          let+ step =
            linearize ~value:(unit_value ~loc:l) ~access_type:e.exp_type ~contents:elt ctx
              ~at how (preparation @ access)
          in
          (stmts @ step, unit_value ~loc:l)
      | _ -> State.of_result (unsupported at ("Atomic." ^ op))
      end

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
        begin match op with
        | Div | Mod ->
            let+ nonzero = nonzero () in
            (stmts @ [ nonzero ], Prelude.runtime_binary ~loc:l op a b)
        | _ -> State.return (stmts, Prelude.runtime_binary ~loc:l op a b)
        end
    | _, Some op, [ a ] -> (
        let+ stmts, a = expr ctx a in
        match op with
        | `Not -> (stmts, R.Expr.not_ ~loc:l a)
        | `Neg -> (stmts, Prelude.runtime_neg ~loc:l a))
    | None, None, _ -> (
        let* path = State.of_result (Source.normalize_value_path e.exp_env ~at path) in
        (* A function over a witness whose calls wait to be helped is called as its
           universal procedure, whose result has the case of the constructor passed. *)
        let* path, declaration, universal =
          match
            List.find ctx.given.specialized_calls ~f:(fun (paths, _, _, _, _) ->
                List.mem paths path ~equal:Path.same)
          with
          | None -> State.return (path, declaration, None)
          | Some (_, position, id, scheme, (result : Datatypes.t)) -> (
              let case =
                match List.nth args position with
                | Some ({ exp_desc = Texp_construct (_, cstr, []); _ } as witness) ->
                    Option.both
                      (List.find result.ctors ~f:(fun c ->
                           String.equal c.ocaml cstr.cstr_name))
                      (Witnesses.witness_type ctx.given.types witness.exp_type)
                | _ -> None
              in
              match case with
              | Some (ctor, (_, witness, arguments)) ->
                  let ordinary =
                    List.filter_map (List.zip_exn witness.indices arguments)
                      ~f:(fun (index, t) -> Option.some_if (not index) t)
                  in
                  let instance =
                    Btype.newgenty
                      (Tconstr
                         ( Path.Pident (Option.value_exn result.id),
                           ordinary,
                           ref Types.Mnil ))
                  in
                  State.return
                    ( Path.Pident id,
                      { declaration with val_type = scheme },
                      Some (instance, Some (List.hd_exn ctor.fields)) )
              | None ->
                  begin match (ctx.given.universal_result, List.nth args position) with
                  | Some own, Some witness when Option.equal Ident.same own.id result.id
                    ->
                      let* _, shape, arguments =
                        State.of_result
                          (Report.expect ~at "A recursive universal call's witness"
                             (Witnesses.witness_type ctx.given.types witness.exp_type))
                      in
                      let ordinary =
                        List.filter_map (List.zip_exn shape.indices arguments)
                          ~f:(fun (index, argument) ->
                            Option.some_if (not index) argument)
                      in
                      let instance =
                        Ctype.newconstr
                          (Path.Pident (Option.value_exn result.id))
                          ordinary
                      in
                      State.return
                        ( Path.Pident id,
                          { declaration with val_type = scheme },
                          Some (instance, None) )
                  | _ ->
                      State.of_result
                        (unsupported at
                           "A call of a function whose calls wait to be helped, with a \
                            witness other than a constructor")
                  end)
        in
        match resolved_call ctx.given.functions ctx.given.libraries path with
        | Some f ->
            (* A universal procedure's occurrence has the universal result for the
               witness's index types, in the witness and as its result. *)
            let occurrence =
              match universal with
              | None -> occurrence
              | Some (instance, _) ->
                  let rec universal_witness t =
                    match
                      (Types.get_desc t, Witnesses.witness_type ctx.given.types t)
                    with
                    | Tpoly (t, []), _ -> universal_witness t
                    | Tconstr (path, arguments, abbrev), Some (_, witness, _) ->
                        Btype.newgenty
                          (Tconstr
                             ( path,
                               List.map2_exn witness.indices arguments
                                 ~f:(fun index argument ->
                                   if index then instance else argument),
                               abbrev ))
                    | _ -> t
                  in
                  let rec returning t =
                    match Types.get_desc t with
                    | Tarrow (label, a, r, c) ->
                        Btype.newgenty
                          (Tarrow (label, universal_witness a, returning r, c))
                    | Tpoly (t, []) -> returning t
                    | _ -> instance
                  in
                  returning occurrence
            in
            let* actual_target, type_instance =
              State.polymorphic_application ~values:args ~environment:e.exp_env ctx ~at
                ~path ~declaration:declaration.val_type ~occurrence ~target:f
            in
            call ~actual_target ?type_instance ?universal ctx e f args
        | None -> (
            match path with
            | Pident _ -> State.of_result (unsupported at "A call of a local function")
            | _ -> State.of_result (unsupported at ("A call of " ^ Path.name path))))
    | _ -> State.of_result (unsupported at "This application")

(** The call of the top-level function [f] with [args], in [e]: a statement, whose result
    is kept in a variable unless it is unit. *)
and call ?actual_target ?type_instance ?universal ctx (e : Typedtree.expression) f
    (ocaml_args : Typedtree.expression list) =
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
  let raw =
    Option.value_map signature ~default:(Raw_contract.of_header None) ~f:(fun signature ->
        signature.procedure_raw)
  in
  let* () =
    if Raw_contract.any raw && List.mem ctx.given.local_calls f ~equal:String.equal then
      State.of_result (unsupported e.exp_loc "Raw boundaries of a local trusted import")
    else State.return ()
  in
  let* evaluated =
    State.all
      (List.rev (List.mapi ocaml_args ~f:(fun i argument -> (i, argument))))
      ~f:(fun (i, argument) ->
        let marked = Raw_contract.argument raw i in
        let* statements, value = expr ~allow_raw:marked ctx argument in
        let+ value =
          if marked then
            State.raw_inject ctx.given ~at:argument.exp_loc ~elt:argument.exp_type value
          else State.return value
        in
        (statements, value))
  in
  let arguments = List.concat_map evaluated ~f:fst in
  let args = List.rev_map evaluated ~f:snd in
  let inputs = Option.value_map signature ~default:[] ~f:(fun s -> s.procedure_inputs) in
  let outputs =
    Option.value_map signature ~default:[] ~f:(fun s -> s.procedure_outputs)
  in
  let returns_value =
    Option.value_map signature
      ~default:(not (is_unit e.exp_type))
      ~f:(fun signature -> signature.procedure_returns_value)
  in
  let annotation =
    List.Assoc.find ctx.given.access_proofs
      (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum)
      ~equal:Poly.equal
  in
  let* capture_outcome =
    match annotation with
    | Some annotation when List.Assoc.mem ctx.given.raising f ~equal:String.equal ->
        State.of_result
          (access_captures_outcome annotation ~outputs:(List.length outputs))
    | _ -> State.return false
  in
  let run explicit =
    call_prepared ?actual_target ?universal ctx e f ocaml_args args ~explicit
      ~capture_outcome ~returns_value ~raw_result:raw.result ~signature_outputs:outputs
  in
  match annotation with
  | None when List.mem ctx.given.local_calls f ~equal:String.equal ->
      let l = loc e.exp_loc in
      let target = Option.value actual_target ~default:f in
      let contract suffix values =
        R.Spec.make (R.Expr.call ~loc:l (qualified_name ~loc:l (target ^ suffix)) values)
      in
      let precondition = R.Stmt.exhale ~loc:l (contract "$local_pre" args) in
      if is_unit e.exp_type then
        State.return
          ( arguments
            @ [ precondition; R.Stmt.inhale ~loc:l (contract "$local_post" args) ],
            unit_value ~loc:l )
      else
        let* result_type = State.typ ctx ~at:e.exp_loc e.exp_type in
        let* result = State.fresh "local_result" in
        let value = R.Expr.var ~loc:l (name ~loc:l result) in
        State.return
          ( arguments
            @ R.Stmt.local ~loc:l ~typ:result_type (ident ~loc:l result)
            @ [
                precondition;
                R.Stmt.havoc ~loc:l (name ~loc:l result);
                R.Stmt.inhale ~loc:l (contract "$local_post" (args @ [ value ]));
              ],
            value )
  | None ->
      let+ statements, value, _, after_call = run None in
      (arguments @ statements @ after_call, value)
  | Some annotation ->
      let+ statements, value =
        access_proof ctx annotation ~result_type:e.exp_type
          ~input_types:(List.map inputs ~f:snd)
          ~output_types:
            (List.map outputs ~f:snd @ if capture_outcome then [ outcome_type ] else [])
          (fun values -> run (Some values))
      in
      (arguments @ statements, value)

and call_prepared ?actual_target ?universal ctx (e : Typedtree.expression) f ocaml_args
    args ~explicit ~capture_outcome ~returns_value ~raw_result ~signature_outputs =
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
  let* () =
    State.of_result
      (if
         List.exists prefix ~f:(fun value ->
             List.exists s.carried.raw_values ~f:(fun (_, carrier) ->
                 R.Expr.alpha_equal value carrier))
       then unsupported e.exp_loc "Implicit continuation parameters carrying raw payloads"
       else Ok ())
  in
  let* captured =
    State.of_result (captured_arguments ~at:e.exp_loc ~values:[] s.names captured)
  in
  let* captured_checks = State.all captured ~f:(State.check_raw ~at:e.exp_loc) in
  let stmts = stmts @ List.concat captured_checks in
  let prefix = prefix @ captured in
  let* ghosts =
    Call_witnesses.infer_ghost_inputs ctx ~at:e.exp_loc ~callee:f
      ~ocaml_args:(List.map ocaml_args ~f:Option.some)
      ~prefix_count:(List.length prefix) ~explicit
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
      when List.Assoc.mem ctx.given.atomic_procedures f ~equal:String.equal
           && Poly.equal au_state (Some Pending) ->
        let forward =
          Option.exists
            (Option.bind
               (List.Assoc.find ctx.given.atomic_procedures f ~equal:String.equal)
               ~f:(fun target ->
                 List.Assoc.find s.tables.procedure_implicits target ~equal:String.equal))
            ~f:(List.equal String.equal au.implicit_names)
        in
        let+ opened = open_for_call au ~at:e.exp_loc in
        Option.map opened ~f:(fun (opening, values) ->
            (au, opening, if forward then values else []))
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
  let* witnesses =
    Call_witnesses.history_inputs ctx ~at:e.exp_loc ~callee:f
      ~argument_types:
        (List.map ocaml_args ~f:(fun (e : Typedtree.expression) -> e.exp_type))
      ~prefix_count:(List.length prefix) ~args
  in
  (* A library's procedure is qualified by its module, as [Backoff.once]. *)
  let callee_name = qualified_name ~loc:l (Option.value actual_target ~default:f) in
  let* execution_statements, execution_arguments =
    if
      execution_enabled ctx.given
      && List.exists ctx.given.functions.entries ~f:(fun (_, target) ->
          String.equal target f)
    then State.execution_arguments ctx ~at:e.exp_loc
    else State.return ([], [])
  in
  let stmts = stmts @ execution_statements in
  let callee =
    R.Expr.call ~loc:l callee_name (args @ witnesses @ execution_arguments @ implicit)
  in
  let reuse = Option.map retry ~f:(fun (au, _, _) -> au.ghost_results) in
  let* ghost_decls, ghosts =
    Call_witnesses.history_outputs ?reuse ctx ~at:e.exp_loc ~callee:f
      ~argument_types:
        (List.map ocaml_args ~f:(fun (e : Typedtree.expression) -> e.exp_type))
      ~prefix_count:(List.length prefix) ~result_type:e.exp_type ~args
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
  let public_values =
    public_values @ if capture_outcome then Option.to_list outcome_value else []
  in
  let propagation, after_call =
    if capture_outcome then ([], propagation) else (propagation, [])
  in
  if is_unit e.exp_type && not returns_value then
    let+ closing = closing (unit_value ~loc:l) outcome_value in
    let call =
      match ghosts with
      | [] -> [ R.Stmt.call ~loc:l callee ]
      | _ -> ghost_decls @ [ R.Stmt.assign ~loc:l ghosts (R.Stmt.expr_rhs callee) ]
    in
    ( stmts @ opening @ call @ closing @ propagation,
      unit_value ~loc:l,
      public_values,
      after_call )
  else
    (* A call of a universal procedure returns its universal result, of which the value
       is the case of the call's witness. *)
    let* typ =
      State.typ ctx ~at:e.exp_loc
        (if raw_result then Predef.type_option e.exp_type
         else Option.value_map universal ~default:e.exp_type ~f:fst)
    in
    let* x = State.fresh "tmp" in
    let result = R.Expr.var ~loc:l (name ~loc:l x) in
    let v =
      Option.value_map universal ~default:result ~f:(fun (_, field) ->
          Option.value_map field ~default:result ~f:(fun field ->
              R.Expr.field ~loc:l result (qualified_name ~loc:l field)))
    in
    let def =
      match ghosts with
      | [] -> R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs callee) (ident ~loc:l x)
      | _ ->
          R.Stmt.local ~loc:l ~typ (ident ~loc:l x)
          @ ghost_decls
          @ [ R.Stmt.assign ~loc:l (result :: ghosts) (R.Stmt.expr_rhs callee) ]
    in
    let* closing = closing v outcome_value in
    if not raw_result then
      State.return
        (stmts @ opening @ def @ closing @ propagation, v, public_values, after_call)
    else
      let* typ = State.typ ctx ~at:e.exp_loc e.exp_type in
      let* projected_name = State.fresh "raw_result" in
      let projected = R.Expr.var ~loc:l (name ~loc:l projected_name) in
      let+ () = State.register_raw projected result in
      ( stmts @ opening @ def @ closing @ propagation
        @ R.Stmt.local ~loc:l ~const:true ~typ
            ~init:(R.Stmt.expr_rhs (State.raw_project ~loc:l result))
            (ident ~loc:l projected_name),
        projected,
        public_values,
        after_call )

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
and operands ?(continue_state = false) ctx (args : Typedtree.expression list) =
  let+ evaluated =
    State.all (List.rev args) ~f:(fun arg -> expr ~continue_state ctx arg)
  in
  (List.concat_map evaluated ~f:fst, List.rev_map evaluated ~f:snd)

(** A statically known callback runs directly in a list traversal, with no closure value.
*)
and fold_left ctx (e : Typedtree.expression) arguments =
  let at = e.exp_loc in
  let l = loc at in
  let* callback, initial, values =
    match arguments with
    | [ (Nolabel, Arg callback); (Nolabel, Arg initial); (Nolabel, Arg values) ] ->
        State.return (callback, initial, values)
    | _ ->
        State.of_result
          (unsupported at "A partially applied List.fold_left; supply all three arguments")
  in
  let* parameters, body =
    match callback.exp_desc with
    | Texp_function
        ( [
            { fp_arg_label = Nolabel; fp_kind = Tparam_pat accumulator; _ };
            { fp_arg_label = Nolabel; fp_kind = Tparam_pat element; _ };
          ],
          Tfunction_body body ) ->
        State.return ([ accumulator; element ], body)
    | _ ->
        State.of_result
          (unsupported callback.exp_loc
             "A List.fold_left callback other than an inline function with two parameters")
  in
  let* () = no_loop_before_linearizing ~at in
  let* spec, annotation =
    State.of_result
      (loop_spec ~target:at ctx ~after:(List.last_exn parameters).pat_loc body)
  in
  let* setup, arguments = operands ctx [ initial; values ] in
  let initial_value, values_value =
    match arguments with [ initial; values ] -> (initial, values) | _ -> assert false
  in
  let local source_type base value =
    let* typ = State.typ ctx ~at source_type in
    let* () = State.note_domain ctx.given.types source_type in
    let+ variable =
      State.bind_name ~typ:source_type ~base (Ident.create_local ("caravan$" ^ base))
    in
    ( variable,
      R.Expr.var ~loc:l (name ~loc:l variable),
      R.Stmt.local ~loc:l ~const:false ~typ ~init:(R.Stmt.expr_rhs value)
        (ident ~loc:l variable) )
  in
  let* accumulator, accumulator_value, accumulator_decl =
    local initial.exp_type "fold_accumulator" initial_value
  in
  let* remaining, remaining_value, remaining_decl =
    local values.exp_type "fold_remaining" values_value
  in
  let* raising = loop_raising ctx ~at ~spec None body in
  let guard = Option.map raising ~f:(fun (_, _, _, guard, _) -> guard) in
  let decl, exceptional =
    Option.value_map raising ~default:([], []) ~f:(fun (decl, _, _, _, terms) ->
        (decl, terms))
  in
  let* invariants =
    loop_invariants
      ~inputs:
        [ (accumulator_value, initial.exp_type); (remaining_value, values.exp_type) ]
      ?guard ?annotation ctx ~at spec
      ~relation:(fun _ -> State.return None)
  in
  let* loop_scope = State.get_scope in
  let* body_stmts, reaching =
    in_loop raising (fun () ->
        let head = R.Expr.field ~loc:l remaining_value (qualified_name ~loc:l "hd") in
        let* bindings =
          State.all
            (List.zip_exn parameters [ accumulator_value; head ])
            ~f:(fun (parameter, value) ->
              let* reading, condition, bindings = pattern ctx parameter value in
              let* () =
                match condition with
                | None -> State.return ()
                | Some _ ->
                    State.of_result
                      (unsupported parameter.pat_loc "A refutable fold callback parameter")
              in
              let* definitions =
                State.all bindings ~f:(fun (id, value, source_type) ->
                    let* typ = State.typ ctx ~at source_type in
                    let* () = State.note_domain ctx.given.types source_type in
                    let+ variable = State.bind_name ~typ:source_type id in
                    R.Stmt.local ~loc:l ~const:true ~typ ~init:(R.Stmt.expr_rhs value)
                      (ident ~loc:l variable)
                    @ assert_admissible ctx ~loc:l source_type variable)
              in
              let+ () = record_projection_bindings parameter value in
              reading @ List.concat definitions)
        in
        let* body_stmts, result = expr ctx body in
        let* () = State.set_scope loop_scope in
        State.return
          (List.concat bindings @ body_stmts
          @ [
              assign (accumulator, l) result;
              assign (remaining, l)
                (R.Expr.field ~loc:l remaining_value (qualified_name ~loc:l "tl"));
            ]))
  in
  let* propagation =
    match raising with
    | None -> State.return []
    | Some (_, outcome, typ, _, _) -> propagate ~at ~certain:false ~typ outcome reaching
  in
  let condition =
    R.Expr.not_ ~loc:l (R.Expr.is_ ~loc:l remaining_value (ident ~loc:l "nil"))
  in
  let condition =
    Option.value_map guard ~default:condition ~f:(fun guard ->
        R.Expr.binary ~loc:l And condition guard)
  in
  State.return
    ( setup @ accumulator_decl @ remaining_decl @ decl
      @ [
          R.Stmt.while_ ~loc:l ~invariants:(invariants @ exceptional) condition body_stmts;
        ]
      @ propagation,
      accumulator_value )

(** The accesses and condition for matching [p] against [v], and its bindings. *)
and pattern ?guard ?(allow_raw = false) ctx (p : Typedtree.pattern) (v : R.Expr.t) =
  let binding = match p.pat_desc with Tpat_var _ | Tpat_any -> true | _ -> false in
  let* checked =
    if allow_raw && binding then State.return [] else State.check_raw ~at:p.pat_loc v
  in
  let+ reading, condition, bindings = pattern_body ?guard ctx p v in
  (checked @ reading, condition, bindings)

and pattern_body ?guard ctx (p : Typedtree.pattern) (v : R.Expr.t) =
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
      let record_type = p.pat_type in
      let* parts =
        State.all fields ~f:(fun (_, label, p) ->
            let* field = State.field_of_label ctx.given ~at ~record_type label in
            match field with
            | Some (field, false) ->
                State.return (p, ([], R.Expr.field ~loc:l v (qualified_name ~loc:l field)))
            | Some (field, true) ->
                let+ access, value =
                  State.ordinary_read ?guard
                    ~immutable:(Poly.equal label.lbl_mut Immutable)
                    ctx.given ~at ~field ~elt:p.pat_type v
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
      begin match
        occurrence_constructor ~environment:p.pat_env ctx.given.types p.pat_type cstr
      with
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
and match_cases ?(raw = false) ?commits ?otherwise ?arm ~tail ctx ~at v
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
  let case_body ?source_pattern ?(names = enclosing_names) join binds
      (rhs : Typedtree.expression) =
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
         let* () =
           match source_pattern with
           | None -> State.return ()
           | Some pattern -> record_projection_bindings pattern v
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
         let* stmts, value = expr ~tail ~allow_raw:raw rhs_ctx rhs in
         let value =
           Option.value_map conversion ~default:value ~f:(fun conversion ->
               R.Expr.call ~loc:l
                 (Qualified_name.raven ~loc:l (Qualified_name.of_string conversion))
                 [ value ])
         in
         let* finish = finish_arm ctx ~tail value in
         let* value =
           branch_value ctx ~raw ~at:rhs.exp_loc ~elt:rhs.exp_type ~target value
         in
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
              let+ body, join, ended = case_body ~source_pattern:p join binds rhs in
              (access @ body, join, ended :: ends)
          | (p, rhs) :: rest -> begin
              let* access, cond, binds = pattern ctx p v in
              let* body, join, ended = case_body ~source_pattern:p join binds rhs in
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
    | ((p : Typedtree.pattern), _) :: _
      when Option.is_some
             (Datatypes.indexed_instance ctx.given.types
                (Datatypes.expand ctx.given.types p.pat_type)) ->
        None
    | ((p : Typedtree.pattern), rhs) :: rest ->
        begin match p.pat_desc with
        | Tpat_construct (_, cstr, ps, _) ->
            begin match
              ( occurrence_constructor ~environment:p.pat_env ctx.given.types p.pat_type
                  cstr,
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
and conditional_arms ?(raw = false) ctx ~at ?polarity ~tail c (e1 : Typedtree.expression)
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
         | None ->
             let* finish = finish_arm ctx ~tail (unit_value ~loc:l) in
             let+ value =
               branch_value ctx ~raw ~at ~elt:Predef.type_unit ~target (unit_value ~loc:l)
             in
             finish
             @ Option.value_map target ~default:[] ~f:(fun target ->
                 [ assign target value ])
         | Some e ->
             let* stmts, v = expr ~tail ~allow_raw:raw ctx e in
             let* finish = finish_arm ctx ~tail v in
             let+ v = branch_value ctx ~raw ~at:e.exp_loc ~elt:e.exp_type ~target v in
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
and conditional ?(raw = false) ctx ~at ?polarity ~tail c e1 e2 target =
  let* before = pending_count in
  let* stmts = conditional_arms ~raw ctx ~at ?polarity ~tail c e1 e2 target in
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
      (Exceptions.uses
         ~key:(Exceptions.key ctx.given.types)
         ~application_raises:(Domain_calls.application_raises ctx.given.domain_calls)
         e)
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

(** A join is speculative only when one of its source arms is speculative. *)
and branch_value ctx ~raw ~at ~elt ~target value =
  if not raw then State.return value
  else
    let* speculative = State.raw_value value in
    let* () =
      match (speculative, target) with
      | Some _, Some (target, _) ->
          State.modify_carried (fun carried ->
              { carried with raw_joins = Set.add carried.raw_joins target })
      | _ -> State.return ()
    in
    State.raw_inject ctx.given ~at ~elt value

(** The statements [make target] computing the value of [e] into a new variable [target],
    and that variable; no variable if [e] is of type unit. *)
and branch ?(raw = false) ctx (e : Typedtree.expression) make =
  let l = loc e.exp_loc in
  if is_unit e.exp_type && not raw then
    let+ stmts = make None in
    (stmts, unit_value ~loc:l)
  else
    let* typ =
      State.typ ctx ~at:e.exp_loc
        (if raw then Predef.type_option e.exp_type else e.exp_type)
    in
    let* x = State.fresh "tmp" in
    let* stmts = make (Some (x, l)) in
    let value = R.Expr.var ~loc:l (name ~loc:l x) in
    let statements = R.Stmt.local ~loc:l ~const:false ~typ (ident ~loc:l x) @ stmts in
    if not raw then State.return (statements, value)
    else
      let* payload_type = State.typ ctx ~at:e.exp_loc e.exp_type in
      let* payload_name = State.fresh "raw_join" in
      let payload = R.Expr.var ~loc:l (name ~loc:l payload_name) in
      let* speculative =
        State.gets (fun (state : State.state) -> Set.mem state.carried.raw_joins x)
      in
      let+ () =
        if speculative then State.register_raw payload value else State.return ()
      in
      ( statements
        @ R.Stmt.local ~loc:l ~const:true ~typ:payload_type
            ~init:(R.Stmt.expr_rhs (State.raw_project ~loc:l value))
            (ident ~loc:l payload_name),
        payload )

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
  | Texp_struct_item
      ({ str_desc = Tstr_open { open_expr = { mod_desc = Tmod_ident _; _ }; _ }; _ }, body)
    ->
      pure_in values body
  | Texp_unreachable -> raw_default ctx ~at e.exp_type
  | Texp_ident (Pident id, _, _) ->
      begin match
        ( List.Assoc.find values (Ident.unique_name id) ~equal:String.equal,
          State.name_in names id )
      with
      | Some value, _ ->
          let* raw = State.raw_value value in
          if Option.is_some raw then not_pure "An unvalidated speculative value"
          else State.return value
      | None, Some x ->
          let value = R.Expr.var ~loc:l (name ~loc:l x) in
          let* raw = State.raw_value value in
          if Option.is_some raw then not_pure "An unvalidated speculative value"
          else State.return value
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
      begin match
        occurrence_constructor ~environment:e.exp_env ctx.given.types e.exp_type cstr
      with
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
  | Texp_field (({ exp_desc = Texp_ident (Pident r, _, _); _ } as record), _, label)
    when Option.is_some (State.name_in names r) -> begin
      let* field =
        State.field_of_label ctx.given ~at ~record_type:record.exp_type label
      in
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
      let* field =
        State.field_of_label ctx.given ~at ~record_type:record.exp_type label
      in
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
      let* args = State.of_result (supplied_args ~at args) in
      let* () =
        if polymorphic_ordering ctx path args then
          State.of_result (unsupported at "Ordering on polymorphic values")
        else State.return ()
      in
      let* args = State.all args ~f:(pure_in values) in
      match (binop_of_path path, unop_of_path path, path, args) with
      | Some op, _, _, [ a; b ] -> State.return (Prelude.runtime_binary ~loc:l op a b)
      | _, Some `Not, _, [ a ] -> State.return (R.Expr.not_ ~loc:l a)
      | _, Some `Neg, _, [ a ] -> State.return (Prelude.runtime_neg ~loc:l a)
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
              let* raw_captures = State.all captured ~f:State.raw_value in
              let* () =
                if List.exists raw_captures ~f:Option.is_some then
                  not_pure "An unvalidated speculative capture"
                else State.return ()
              in
              let+ actual_target =
                State.polymorphic_call ~environment:e.exp_env ctx ~at ~path
                  ~declaration:declaration.val_type ~occurrence:callee.exp_type ~target:f
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
