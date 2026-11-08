(** Ghost inputs and history witnesses shared by calls and domain tasks. *)

open Base
open Translate_context
open Proof_terms
open Atomic_proofs
open State.Syntax

let infer_ghost_inputs ctx ~at ~callee ~(ocaml_args : Typedtree.expression option list)
    ~prefix_count ~explicit =
  let l = loc at in
  let* (s : State.state) = State.get in
  match explicit with
  | Some values -> State.return values
  | None ->
      State.of_result
        (all
           (Option.value
              (List.Assoc.find ctx.given.ghost_args callee ~equal:String.equal)
              ~default:[])
           ~f:(fun equation ->
             let known =
               Option.bind equation ~f:(fun (i, field) ->
                   match Option.join (List.nth ocaml_args (i - prefix_count)) with
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
                 error at
                   "Caravan cannot tell the ghost argument of this call: give the callee \
                    a precondition that makes a parameter a field of it, as tail = \
                    q.tail"
             | None, Some (_, field) ->
                 error at
                   (Printf.sprintf
                      "Caravan cannot tell the ghost argument of this call: the argument \
                       is not a variable known to be the field %s of a value, as one a \
                       record pattern binds"
                      field)))

let history_inputs ctx ~at ~callee ~argument_types ~prefix_count ~args =
  let l = loc at in
  (* The latest snapshot witnesses the facts about earlier states that the callee
     requires, with the arguments' positions in it. *)
  let* path = get_path in
  let* env = scope_env ctx in
  let argument_type index = List.nth argument_types (index - prefix_count) in
  let* witnesses =
    State.all
      (Option.value
         (List.Assoc.find ctx.given.pasts callee ~equal:String.equal)
         ~default:[])
      ~f:(fun (inv, field, i) ->
        let* st =
          resolve_shared_structure ?element_type:(argument_type i) env ~at ~invariant:inv
            ~field
        in
        let inv = st.invariant in
        let* argument =
          State.of_result
            (Report.expect ~at "The argument a past fact is about" (List.nth args i))
        in
        match
          ( List.Assoc.find path.snapshots inv ~equal:String.equal,
            known_position path.positions inv field argument )
        with
        | _, Some p -> State.return [ p.pos_snapshot; p.pos_k ]
        | Some (latest :: _), None ->
            let+ index =
              State.of_result
                (Report.expect ~at
                   ("The snapshot index of field " ^ field)
                   (List.Assoc.find latest.indices field ~equal:String.equal))
            in
            [
              state_of ~loc:l st (grown st latest.values);
              R.Expr.index ~loc:l index argument;
            ]
        | _ ->
            State.of_result
              (error at
                 "This call needs a fact about an earlier state, of which no snapshot \
                  was taken"))
  in
  State.return (List.concat witnesses)

let history_outputs ?reuse ctx ~at ~callee ~argument_types ~prefix_count ~result_type
    ~args =
  let l = loc at in
  let* env = scope_env ctx in
  (* The ghost results witnessing facts about the state after the call: the caller's own,
     if the callee continues its update with the same ones. *)
  let* ghost_facts =
    let metadata =
      Option.value
        (List.Assoc.find ctx.given.past_returns callee ~equal:String.equal)
        ~default:[]
    in
    State.all metadata ~f:(fun past ->
        let parameters = past.past_inputs @ [ past.past_result; past.past_element ] in
        let* worker =
          State.of_result
            (Generic_parameters.discover ~expand:(Datatypes.expand env.data)
               ~key:past.past_invariant ~name:past.past_invariant ~at
               ~explicit:(List.length past.past_inputs)
               parameters)
        in
        let* element_type =
          if List.is_empty worker.variables then State.return past.past_element
          else
            let* () =
              if List.length past.past_inputs = prefix_count + List.length argument_types
              then State.return ()
              else
                State.of_result
                  (unsupported at "This lifted history call's type arguments")
            in
            let* arguments =
              State.of_result
                (Generic_parameters.instantiate ~environment:env.ctx.given.env
                   ~opaque:(Datatypes.is_opaque env.data)
                   ~expand:(Datatypes.expand env.data) ~at worker
                   (List.init prefix_count ~f:(fun _ -> None)
                   @ List.map argument_types ~f:Option.some
                   @ [ Some result_type; None ]))
            in
            State.return
              (List.last_exn (Generic_parameters.parameter_types worker arguments))
        in
        let+ st =
          resolve_shared_structure ~element_type env ~at ~invariant:past.past_invariant
            ~field:past.past_field
        in
        { past with past_invariant = st.invariant; past_element = element_type })
  in
  let ghost_count = 2 * List.length ghost_facts in
  let* ghost_decls, ghosts =
    match reuse with
    | Some values when ghost_count > 0 && List.length values = ghost_count ->
        State.return ([], values)
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
  State.return (ghost_decls, ghosts)
