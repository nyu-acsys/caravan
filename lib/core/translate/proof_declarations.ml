(** Proof declarations: action checks, lemmas, predicates, proof functions, scoped
    resources and generic modules. *)

open Base
open Translate_context
open Spec_terms
open Proof_terms
open Atomic_proofs
open Procedures
open Program_items

(** The lemmas checking that the actions of [st] keep its history's order: that each makes
    no field marked [@grows] shrink. The action's parameters have the types that its
    step's arguments give them; an action whose parameters are not all typed so is not
    checked. *)
let action_checks ctx (st : structure) =
  let open State.Syntax in
  if not (has_history st) then State.return []
  else
    State.map ~f:List.concat
    @@ State.all st.actions ~f:(fun a ->
        let at = a.action_at in
        let l = loc at in
        let var x = R.Expr.var ~loc:l (name ~loc:l x) in
        let* fields =
          State.all st.fields ~f:(fun (f, _, typ, t, _) ->
              let+ raven = State.fresh f in
              (f, raven, typ, t))
        in
        let* indices =
          State.all st.chains ~f:(fun (field, _) ->
              let+ raven = State.fresh (field ^ "_index") in
              (field, raven, chain_index_type ctx.given.types st field))
        in
        let* params =
          State.all st.params ~f:(fun (x, t) ->
              let* typ = State.of_result (typ ctx ~at t) in
              let+ raven = State.fresh x in
              (x, raven, t, typ))
        in
        let args = List.map params ~f:(fun (_, raven, _, _) -> var raven) in
        let* scope_env = scope_env ctx in
        let env =
          let env =
            bind scope_env st.state
              (State (List.map fields ~f:(fun (f, raven, _, t) -> (f, (var raven, t)))))
          in
          List.fold params ~init:env ~f:(fun env (x, raven, t, _) ->
              { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
        in
        (* The types of the parameters, from the step's arguments. *)
        let rec typed (pattern : S.term) (t : Types.type_expr) =
          match spine (S.chain pattern) [] with
          | { term_desc = Tvar (Qid { pid_str = x; _ }); _ }, []
            when List.mem a.params x ~equal:String.equal ->
              [ (x, t) ]
          | ( { term_desc = Tvar (Qid { pid_str = "([])"; _ }); _ },
              [ _; { term_desc = Tvar (Qid { pid_str = k; _ }); _ } ] )
            when List.mem a.params k ~equal:String.equal ->
              [ (k, Predef.type_int) ]
          | { term_desc = Tvar (Qid { pid_str = c; _ }); _ }, ctor_args
            when Char.is_uppercase c.[0] -> begin
              let ctor_args =
                match ctor_args with
                | [ { term_desc = Ttuple ts; _ } ] -> ts
                | _ -> ctor_args
              in
              match find_constructor env (S.Qid (S.mk_id ~loc:pattern.term_loc c)) with
              | Some (_, ctor) when List.length ctor.args = List.length ctor_args ->
                  List.concat (List.map2_exn ctor_args ctor.args ~f:typed)
              | _ -> []
            end
          | _ -> []
        in
        let param_types =
          match a.step with
          | Some (_, Some location :: patterns) ->
              begin match
                Option.map (term_type env location) ~f:(Datatypes.desc ctx.given.types)
              with
              | Some (Tconstr (p, [ contents ], _)) when Datatypes.is_atomic p ->
                  List.concat_map patterns ~f:(function
                    | Some pattern -> typed pattern contents
                    | None -> [])
              | _ -> []
              end
          | _ -> []
        in
        let* typed_params =
          State.all a.params ~f:(fun x ->
              match List.Assoc.find param_types x ~equal:String.equal with
              | Some t ->
                  let+ raven = State.fresh x in
                  Some (x, raven, t)
              | None -> State.return None)
        in
        match Option.all typed_params with
        | None -> State.return []
        | Some action_params ->
            let* action_vars =
              State.all action_params ~f:(fun (_, raven, t) ->
                  let+ typ = State.of_result (typ ctx ~at t) in
                  R.Var.make ~loc:l (ident ~loc:l raven) typ)
            in
            let opened =
              {
                values = List.map fields ~f:(fun (_, raven, _, _) -> var raven);
                indices =
                  List.map indices ~f:(fun (field, raven, _) -> (field, var raven));
              }
            in
            let performing =
              {
                performed = a;
                bindings = List.map action_params ~f:(fun (x, raven, _) -> (x, var raven));
              }
            in
            let* next, _, _ =
              next_state ctx st ~inv_params:st.params args opened performing
            in
            let state values = state_of ~loc:l st (grown st values) in
            (* Reported at the return point of the lemma, at the end of the action's
               name. *)
            let+ () =
              State.record_origin
                {
                  at = { at with loc_start = at.loc_end };
                  code = Postcondition;
                  message =
                    Printf.sprintf "The action %s may make a field marked [@grows] shrink"
                      a.action;
                  related = [];
                }
            in
            [
              R.Member.callable
                (R.Callable.proc ~loc:l ~kind:Lemma
                   ~formals:
                     (List.map params ~f:(fun (_, raven, _, typ) ->
                          R.Var.make ~loc:l (ident ~loc:l raven) typ)
                     @ List.map fields ~f:(fun (_, raven, typ, _) ->
                         R.Var.make ~loc:l (ident ~loc:l raven) typ)
                     @ List.map indices ~f:(fun (_, raven, typ) ->
                         R.Var.make ~loc:l (ident ~loc:l raven) typ)
                     @ action_vars)
                   ~ensures:
                     [
                       R.Spec.make
                         (R.Expr.call ~loc:l
                            (qualified_name ~loc:l (member_name st "extends"))
                            [ state opened.values; state (List.map next ~f:fst) ]);
                     ]
                   (generated_ident ~loc:l (member_name st (a.action ^ "_grows")))
                   (Some []));
            ])

(** The context translating the specifications of declarations, outside functions. *)
let spec_context types ~shared ~ocaml_env ~preds ~spec_funcs
    ?(proof_support = empty_proof_support) () =
  {
    given =
      declaration_inputs types ~shared ~env:ocaml_env ~preds ~spec_funcs ~proof_support ();
    au = None;
  }

(** Recursive proof calls need checked well-founded descent, including mutual calls. *)
let check_lemma_recursion ?(resolve = fun _ q -> qualid_key q) declarations =
  let rec calls at bound (body : S.proof_expr) =
    match body.proof_desc with
    | Proof_value t ->
        let head, _ = spine t [] in
        begin match head.term_desc with
        | Tvar (Qid id) when List.mem bound id.pid_str ~equal:String.equal -> []
        | Tvar q -> [ resolve at q ]
        | _ -> []
        end
    | Proof_let (pattern, rhs, body) ->
        calls at bound rhs @ calls at (pat_names pattern @ bound) body
    | Proof_seq (rhs, body) -> calls at bound rhs @ calls at bound body
    | Proof_if (_, yes, no) -> calls at bound yes @ calls at bound no
    | Proof_match (_, cases) ->
        List.concat_map cases ~f:(fun (pattern, body) ->
            calls at (pat_names pattern @ bound) body)
    | Proof_fold _ | Proof_unfold _ | Proof_assert _ -> []
  in
  let graph =
    List.filter_map declarations ~f:(function
      | S.Proof_lemma { lemma_name; lemma_params; lemma_body; _ } ->
          Some
            ( lemma_name.pid_str,
              calls lemma_name.pid_loc
                (List.map lemma_params ~f:(fun (id, _) -> id.S.pid_str))
                lemma_body )
      | _ -> None)
  in
  let cyclic start =
    let rec visit seen = function
      | [] -> false
      | x :: pending when String.equal x start -> true
      | x :: pending when List.mem seen x ~equal:String.equal -> visit seen pending
      | x :: pending ->
          let next =
            Option.value (List.Assoc.find graph x ~equal:String.equal) ~default:[]
          in
          visit (x :: seen) (next @ pending)
    in
    visit [] (Option.value (List.Assoc.find graph start ~equal:String.equal) ~default:[])
  in
  Result.all_unit
    (List.map declarations ~f:(function
      | S.Proof_lemma { lemma_name; lemma_variant = []; _ } when cyclic lemma_name.pid_str
        ->
          error lemma_name.pid_loc "A recursive lemma needs a variant"
      | _ -> Ok ()))

(** Checked proof declarations share logical types, but introduce no runtime code. *)
let proof_lemma types ~shared ~ocaml_env ~preds ~spec_funcs ~proof_lemmas ~proof_support
    ~predicate_bodies ?member_name declaration =
  match declaration with
  | S.Proof_lemma
      {
        lemma_name;
        lemma_params;
        lemma_returns;
        lemma_requires;
        lemma_ensures;
        lemma_variant;
        lemma_body;
      } ->
      let ctx =
        let base = spec_context types ~shared ~ocaml_env ~preds ~spec_funcs () in
        {
          base with
          given = { base.given with proof_lemmas; proof_support; predicate_bodies };
        }
      in
      State.in_procedure
      @@
      let open State.Syntax in
      let l = loc lemma_name.pid_loc in
      let signature =
        List.Assoc.find_exn proof_lemmas lemma_name.pid_str ~equal:String.equal
      in
      let declare ?(implicit = false) (id, _) ty =
        let* raven_type = State.of_result (typ ctx ~at:id.S.pid_loc ty) in
        let+ raven = State.fresh id.pid_str in
        ( id.pid_str,
          raven,
          ty,
          R.Var.make ~loc:(loc id.pid_loc) ~ghost:true ~implicit (ident ~loc:l raven)
            raven_type )
      in
      let* inputs =
        State.all (List.zip_exn lemma_params signature.lemma_inputs)
          ~f:(fun (parameter, ty) ->
            declare
              ~implicit:
                (List.mem (fst parameter).S.pid_attrs "implicit" ~equal:String.equal)
              parameter ty)
      in
      let* outputs =
        State.all (List.zip_exn lemma_returns signature.lemma_outputs)
          ~f:(fun (parameter, ty) -> declare parameter ty)
      in
      let parameters = inputs @ outputs in
      let* () =
        match
          List.find_a_dup
            (List.map parameters ~f:(fun (x, _, _, _) -> x))
            ~compare:String.compare
        with
        | None -> State.return ()
        | Some x ->
            State.of_result
              (error lemma_name.pid_loc (Printf.sprintf "Duplicate proof variable %s" x))
      in
      let env =
        {
          ctx;
          logical_definition = false;
          data = types;
          funcs = spec_funcs;
          var_types = List.map parameters ~f:(fun (x, _, ty, _) -> (x, ty));
          vars = List.map parameters ~f:(fun (x, raven, _, _) -> (x, Raven raven));
        }
      in
      let specs terms =
        State.all terms ~f:(fun t ->
            let+ value = formula env t in
            R.Spec.make value)
      in
      let* requires = specs lemma_requires in
      let* ensures = specs lemma_ensures in
      let* decreases = State.all lemma_variant ~f:(formula env) in
      let body_env =
        {
          env with
          vars = List.map inputs ~f:(fun (x, raven, _, _) -> (x, Raven raven));
          var_types = List.map inputs ~f:(fun (x, _, ty, _) -> (x, ty));
        }
      in
      let targets =
        List.map outputs ~f:(fun (_, raven, ty, _) ->
            { target_name = raven; target_type = ty })
      in
      let+ body = proof_expression body_env targets lemma_body in
      R.Callable.proc ~loc:l ~kind:Lemma
        ~formals:(List.map inputs ~f:(fun (_, _, _, v) -> v))
        ~returns:(List.map outputs ~f:(fun (_, _, _, v) -> v))
        ~requires ~ensures ~decreases
        (ident ~loc:l (Option.value member_name ~default:lemma_name.pid_str))
        (Some body)
  | _ -> State.of_result (error Location.none "Expected a lemma declaration")

(** The predicate [p], declared at [at], whose parameters have the OCaml types
    [param_types], defined as [def]. Each stateful invariant holds half of its views. *)
let predicate types ~shared ~ocaml_env ~preds ~spec_funcs ~proof_support ?declaration_name
    ~at ~structures (p : S.predicate) (def : definition) param_types :
    R.Callable.t State.t =
  let ctx = spec_context types ~shared ~ocaml_env ~preds ~spec_funcs ~proof_support () in
  State.in_procedure
  @@
  let open State.Syntax in
  let l = loc at in
  let* params, env = pred_params ctx ~at p param_types in
  let vars = List.map ~f:(fun (_, _, _, v) -> v) in
  let name = ident ~loc:l (Option.value declaration_name ~default:p.pred_name.pid_str) in
  match def with
  | Direct_invariant body ->
      let+ body = quantified env body in
      R.Callable.func ~loc:l ~kind:Inv ~formals:(vars params) name (Some body)
  | Body body ->
      let* body = quantified env body in
      let+ implicit = State.of_result (implicit_parameters p) in
      let explicit, implicit = List.split_n params (List.length params - implicit) in
      R.Callable.func ~loc:l ~kind:Pred ~inline:p.pred_inline ~formals:(vars explicit)
        ~returns:(vars implicit) name (Some body)
  | View _ ->
      (* Half of the view's ghost field, on the structure, its first parameter. *)
      let inputs, value = List.split_n params (List.length params - 1) in
      let structure, _, structure_type, _ = List.hd_exn params in
      let+ structure =
        formula env (S.mk_term (Tvar (Qid (S.mk_id ~loc:at structure))) at)
      in
      let structure =
        match anchor types structure_type with
        | Some (_, at) -> at ~loc:l structure
        | None -> structure
      in
      let _, raven, _, _ = List.hd_exn value in
      let field =
        R.Expr.field ~loc:l structure
          (qualified_name ~loc:l (view_field_in ctx.given.shared p.pred_name.pid_str))
      in
      R.Callable.func ~loc:l ~kind:Pred ~formals:(vars inputs) ~returns:(vars value) name
        (Some
           (R.Expr.own ~loc:l
              [
                field;
                R.Expr.var ~loc:l (R.Name.make ~loc:l raven);
                R.Expr.real ~loc:l 0.5;
              ]))
  | Invariant { state; body; _ } ->
      (* The state's fields are existentials, as are the index maps of the fields owned by
         index; its views hold the other halves of their ghost fields, and its history
         the authority over the states it extends. *)
      let* st =
        match
          List.find structures ~f:(fun st ->
              String.equal st.invariant p.pred_name.pid_str)
        with
        | Some st -> State.return st
        | None -> State.of_result (error at "An invariant without a state")
      in
      let views = st.views in
      let var x = R.Expr.var ~loc:l (R.Name.make ~loc:l x) in
      let state_env =
        bind env state
          (State (List.map st.fields ~f:(fun (f, raven, _, t, _) -> (f, (var raven, t)))))
      in
      let length s =
        R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ "Seq" ] "length") [ s ]
      in
      let bin op a b = R.Expr.binary ~loc:l op a b in
      (* Ownership of a field's entries by index, as ownership by entry, with the entries'
         positions in a map, which makes them distinct. *)
      let chain (i, guard, field, value) =
        let raven, otyp =
          match List.find st.fields ~f:(fun (f, _, _, _, _) -> String.equal f field) with
          | Some (_, raven, _, t, _) -> (raven, t)
          | None -> (field, Predef.type_int)
        in
        let index = var (List.Assoc.find_exn st.chains field ~equal:String.equal) in
        let entries = var raven in
        let* elt, elt_typ =
          match Datatypes.desc types otyp with
          | Tconstr (_, [ elt ], _) ->
              let+ elt_typ = State.of_result (typ ctx ~at elt) in
              (elt, elt_typ)
          | _ -> State.of_result (error at "A sequence owned by index")
        in
        let* j = State.fresh "i" in
        let* c = State.fresh "c" in
        let wf =
          R.Expr.forall ~loc:l
            ~triggers:[ [ R.Expr.index ~loc:l entries (var j) ] ]
            [ R.Var.make ~loc:l (ident ~loc:l j) (R.Type.int ~loc:l) ]
            (bin Impl
               (bin And
                  (bin Leq (R.Expr.int ~loc:l 0) (var j))
                  (bin Lt (var j) (length entries)))
               (bin Eq
                  (R.Expr.index ~loc:l index (R.Expr.index ~loc:l entries (var j)))
                  (var j)))
        in
        let position = R.Expr.index ~loc:l index (var c) in
        let entry_env =
          {
            (bind state_env i.S.pid_str (Value position)) with
            var_types = (i.pid_str, Predef.type_int) :: state_env.var_types;
          }
        in
        let* guard = formula entry_env guard in
        let contents =
          match Datatypes.desc types elt with
          | Tconstr (_, [ contents ], _) -> Some contents
          | _ -> None
        in
        let* value = expected_formula entry_env contents value in
        let* field = State.field_of_type ctx.given ~at elt "" in
        let+ field =
          match field with
          | Some f -> State.return f
          | None -> State.of_result (error at "Entries owned by index are atomics")
        in
        let owned =
          (* No trigger: one on the index map loops with the positions' trigger, through
             the next entry that an entry's value names. *)
          R.Expr.forall ~loc:l
            [ R.Var.make ~loc:l (ident ~loc:l c) elt_typ ]
            (bin Impl
               (bin And
                  (bin And
                     (bin And
                        (bin Leq (R.Expr.int ~loc:l 0) position)
                        (bin Lt position (length entries)))
                     (bin Eq (R.Expr.index ~loc:l entries position) (var c)))
                  guard)
               (R.Expr.own ~loc:l
                  [ R.Expr.field ~loc:l (var c) (qualified_name ~loc:l field); value ]))
        in
        bin And wf owned
      in
      let* body =
        State.all (conjuncts body) ~f:(fun t ->
            match chain_of ~state t with
            | Some ((_, _, field, _) as owned)
              when List.Assoc.mem st.chains field ~equal:String.equal ->
                chain owned
            | _ -> quantified state_env t)
      in
      (* The registered calls, each waiting on a key, helped once the key is not the one
         that the helping action helps any more, and their registrations. *)
      let* waiting =
        State.all st.pendings ~f:(fun p ->
            let registrations = var (st.state ^ "_" ^ p.pending_field) in
            let on = var p.pending_on in
            let hc = R.Expr.var ~loc:l (R.Name.make ~loc:l "hc") in
            let key = R.Expr.index ~loc:l on hc in
            let helping_state, helping_key, _ = p.helping in
            let+ helped_key =
              formula
                (bind state_env helping_state
                   (Option.value_exn
                      (List.Assoc.find state_env.vars state ~equal:String.equal)))
                helping_key
            in
            let pending_field f =
              R.Expr.field ~loc:l hc (qualified_name ~loc:l (pending_name st p f))
            in
            let half f v =
              R.Expr.own ~loc:l [ pending_field f; v; R.Expr.real ~loc:l 0.5 ]
            in
            (* A key that is an entry of a field owned by index is at its position. *)
            let membership =
              List.filter_map st.chains ~f:(fun (field, _) ->
                  match
                    List.find st.fields ~f:(fun (f, _, _, _, _) -> String.equal f field)
                  with
                  | Some (_, entries, _, t, _) ->
                      begin match Datatypes.desc types t with
                      | Tconstr (_, [ elt ], _)
                        when String.equal (Datatypes.tag types elt)
                               (Datatypes.tag types p.key_type) ->
                          let index =
                            R.Expr.index ~loc:l
                              (var
                                 (List.Assoc.find_exn st.chains field ~equal:String.equal))
                              key
                          in
                          Some
                            (List.reduce_exn ~f:(bin And)
                               [
                                 bin Leq (R.Expr.int ~loc:l 0) index;
                                 bin Lt index (length (var entries));
                                 bin Eq (R.Expr.index ~loc:l (var entries) index) key;
                               ])
                      | _ -> None
                      end
                  | None -> None)
            in
            let registered =
              R.Expr.call ~loc:l
                (qualified_name ~loc:l (pending_name st p "registration"))
                (hc :: List.map params ~f:(fun (_, raven, _, _) -> var raven))
            in
            R.Expr.forall ~loc:l
              [ R.Var.make ~loc:l (ident ~loc:l "hc") (R.Type.ref ~loc:l) ]
              (bin Impl (bin In hc registrations)
                 (List.reduce_exn ~f:(bin And)
                    ((half "watched" key :: membership)
                    @ [ half "linked" (bin Neq key helped_key); registered ]))))
      in
      let body = List.reduce_exn (body @ waiting) ~f:(bin And) in
      let _, structure, _, _ = List.hd_exn params in
      let anchored e =
        match anchor types st.structure_type with
        | Some (_, at) -> at ~loc:l e
        | None -> e
      in
      let* halves =
        State.all views ~f:(fun ((v : S.predicate), value) ->
            (* The view's parameters are the invariant's, but for its value. *)
            let view_env =
              List.fold
                (List.zip_exn (List.drop_last_exn v.pred_params) params)
                ~init:state_env
                ~f:(fun env ((id, _), (_, raven, t, _)) ->
                  {
                    (bind env id.S.pid_str (Raven raven)) with
                    var_types = (id.pid_str, t) :: env.var_types;
                  })
            in
            let+ value = formula view_env value in
            let field =
              R.Expr.field ~loc:l
                (anchored (var structure))
                (qualified_name ~loc:l
                   (view_field_in ctx.given.shared v.pred_name.pid_str))
            in
            R.Expr.own ~loc:l [ field; value; R.Expr.real ~loc:l 0.5 ])
      in
      let history =
        if has_history st then
          let qn m x = generated_module_member ~loc:l m x in
          let state_value =
            R.Expr.call ~loc:l
              (qn (module_name st "state") "state")
              (grown st (List.map st.fields ~f:(fun (_, raven, _, _, _) -> var raven)))
          in
          [
            R.Expr.own ~loc:l
              [
                R.Expr.field ~loc:l
                  (anchored (var structure))
                  (qualified_name ~loc:l (member_name st "history"));
                (history_elements ~loc:l shared.history st).auth state_value;
              ];
          ]
        else []
      in
      let body = List.fold (halves @ history) ~init:body ~f:(bin And) in
      let+ ons =
        State.all st.pendings ~f:(fun p ->
            let+ key = State.of_result (typ ctx ~at p.key_type) in
            R.Var.make ~loc:l (ident ~loc:l p.pending_on)
              (R.Type.map ~loc:l (R.Type.ref ~loc:l) key))
      in
      let existentials =
        List.map st.fields ~f:(fun (_, raven, typ, _, _) ->
            R.Var.make ~loc:l (ident ~loc:l raven) typ)
        @ ons
        @ List.map st.chains ~f:(fun (field, raven) ->
            let elt_typ =
              match
                List.find st.fields ~f:(fun (f, _, _, _, _) -> String.equal f field)
              with
              | Some (_, _, _, t, _) ->
                  begin match Datatypes.desc types t with
                  | Tconstr (_, [ elt ], _) -> Result.ok (typ ctx ~at elt)
                  | _ -> None
                  end
              | None -> None
            in
            R.Var.make ~loc:l (ident ~loc:l raven)
              (R.Type.map ~loc:l
                 (Option.value elt_typ ~default:(R.Type.ref ~loc:l))
                 (R.Type.int ~loc:l)))
      in
      let body =
        match existentials with [] -> body | _ -> R.Expr.exists ~loc:l existentials body
      in
      R.Callable.func ~loc:l ~kind:Inv ~formals:(vars params) name (Some body)

(** The predicates of [source], declared in its interface, its proof or its annotations,
    with where they are declared, their definitions, and their parameters' types. A
    predicate declared in the interface without a definition is defined in the proof or an
    annotation, with the same parameters; an invariant in the proof defines a persistent
    predicate, and a view an exclusive one, whose value has the type of the declaration's
    last parameter. *)
let outside_scopes scopes comments =
  List.filter comments ~f:(fun (_, at) ->
      not
        (List.exists scopes ~f:(fun scope ->
             at.Location.loc_start.pos_cnum >= scope.Location.loc_start.pos_cnum
             && at.loc_end.pos_cnum <= scope.loc_end.pos_cnum)))

let direct_source_comments (source : Source.t) =
  outside_scopes
    (List.filter_map source.typed.str_items ~f:(fun item ->
         match item.Typedtree.str_desc with
         | Tstr_module _ | Tstr_modtype _ -> Some item.str_loc
         | _ -> None))
    source.comments

let direct_interface_comments (interface : Source.interface) =
  outside_scopes
    (List.filter_map interface.signature ~f:(fun item ->
         match item.Parsetree.psig_desc with
         | Psig_module _ | Psig_modtype _ -> Some item.psig_loc
         | _ -> None))
    interface.interface_comments

let predicates (source : Source.t) =
  let of_annotations ~interface comments =
    all
      (List.filter
         (Annotation.of_comments comments)
         ~f:(Annotation.predicate_declaration ~interface))
      ~f:(fun a ->
        let* p = Annotation.predicate a in
        Ok (a.loc, p))
  in
  let* declared =
    Option.value_map source.interface ~default:(Ok []) ~f:(fun i ->
        of_annotations ~interface:true (direct_interface_comments i))
  in
  let* annotated = of_annotations ~interface:false (direct_source_comments source) in
  let name (p : S.predicate) = p.pred_name.pid_str in
  let declaration x = List.find declared ~f:(fun (_, p) -> String.equal (name p) x) in
  let states =
    List.filter_map source.proof ~f:(function
      | Proof_state { state_name; state_fields } -> Some (state_name.pid_str, state_fields)
      | _ -> None)
  in
  let* proof =
    all source.proof ~f:(function
      | S.Proof_predicate p ->
          Ok (Some (p.pred_name.pid_loc, p, Option.map p.pred_body ~f:(fun b -> Body b)))
      | Proof_module _ | Proof_definition _ | Proof_state _ | Proof_action _
      | Proof_lemma _ | Proof_type _ | Proof_resource _ | Proof_field _ | Proof_function _
      | Proof_au _ ->
          Ok None
      | Proof_invariant { inv_name; inv_params; inv_state = state, state_type; inv_body }
        ->
          let params, definition =
            match state_type with
            | PTtyapp (Qid t, []) when List.Assoc.mem states t.pid_str ~equal:String.equal
              ->
                let fields = List.Assoc.find_exn states t.pid_str ~equal:String.equal in
                ( inv_params,
                  Invariant
                    {
                      state = state.pid_str;
                      fields;
                      body = inv_body;
                      field_environment = source.env;
                      field_scope = None;
                    } )
            | _ -> (inv_params @ [ (state, state_type) ], Direct_invariant inv_body)
          in
          Ok
            (Some
               ( inv_name.pid_loc,
                 {
                   S.pred_name = inv_name;
                   pred_params = params;
                   pred_body = None;
                   pred_persistent = true;
                   pred_inline = false;
                 },
                 Some definition ))
      | Proof_view { view_name; view_params; view_value } ->
          begin match declaration view_name.pid_str with
          | Some (_, d) when List.length d.pred_params = List.length view_params + 1 ->
              let value = List.last_exn d.pred_params in
              Ok
                (Some
                   ( view_name.pid_loc,
                     {
                       S.pred_name = view_name;
                       pred_params = view_params @ [ value ];
                       pred_body = None;
                       pred_persistent = false;
                       pred_inline = false;
                     },
                     Some (View { value = view_value }) ))
          | Some (at, _) ->
              error view_name.pid_loc
                ~related:[ (at, "Its declaration") ]
                "A view has the parameters of its declaration but the last, its value"
          | None ->
              error view_name.pid_loc
                (Printf.sprintf
                   "The view %s is not declared in the interface, which gives the type \
                    of its value"
                   view_name.pid_str)
          end)
  in
  let proof = List.filter_opt proof in
  let typed (at, (p : S.predicate), def) =
    let* types =
      all p.pred_params ~f:(fun (_, t) -> Source.ocaml_type source.env ~at t)
    in
    let* _ = implicit_parameters p in
    Ok (at, p, def, types)
  in
  let* declared =
    all declared ~f:(fun (at, p) ->
        typed (at, p, Option.map p.pred_body ~f:(fun b -> Body b)))
  in
  let* defined =
    all
      (List.map annotated ~f:(fun (at, p) ->
           (at, p, Option.map p.pred_body ~f:(fun b -> Body b)))
      @ proof)
      ~f:typed
  in
  let with_def =
    List.filter_map ~f:(fun (at, p, def, types) ->
        Option.map def ~f:(fun def -> (at, p, def, types)))
  in
  (* Predicates defined in the interface are defined there. *)
  let defined = with_def declared @ with_def defined in
  let definitions x =
    List.filter defined ~f:(fun (_, p, _, _) -> String.equal (name p) x)
  in
  let same_types a b =
    List.length a = List.length b
    && List.for_all2_exn a b ~f:(fun a b ->
        String.equal
          (Stdlib.Format.asprintf "%a" Printtyp.type_expr a)
          (Stdlib.Format.asprintf "%a" Printtyp.type_expr b))
  in
  let is_invariant = function
    | Direct_invariant _ | Invariant _ -> true
    | Body _ | View _ -> false
  in
  let declaration (at, (p : S.predicate), def, types) =
    match (def, definitions (name p)) with
    | Some _, _ -> Ok ()
    | None, [] ->
        error at
          (Printf.sprintf
             "The predicate %s is not defined: define it in the proof or an annotation"
             (name p))
    | None, (def_at, _, _, def_types) :: _ when not (same_types types def_types) ->
        error def_at
          ~related:[ (at, "Its declaration") ]
          (Printf.sprintf
             "The predicate %s is defined with other parameter types than it is declared \
              with"
             (name p))
    | None, (def_at, _, d, _) :: _ when Bool.(p.pred_persistent <> is_invariant d) ->
        error def_at
          ~related:[ (at, "Its declaration") ]
          (if p.pred_persistent then
             Printf.sprintf "The invariant %s must be defined as an invariant" (name p)
           else
             Printf.sprintf "The predicate %s must be defined as an ordinary predicate"
               (name p))
    | None, (def_at, definition, _, def_types) :: _ ->
        let* declared_implicit = implicit_parameters p in
        let* defined_implicit = implicit_parameters definition in
        if declared_implicit = defined_implicit then Ok ()
        else
          error def_at
            ~related:[ (at, "Its declaration") ]
            (Printf.sprintf
               "The predicate %s has different implicit parameters in its declaration \
                and definition"
               (name p))
  in
  let definition (at, p, _, _) =
    match definitions (name p) with
    | (first, _, _, _) :: _ :: _ when not (Poly.equal first at) ->
        error at
          ~related:[ (first, "Its first definition") ]
          (Printf.sprintf "The predicate %s is defined twice" (name p))
    | _ -> Ok ()
  in
  let* () = Result.all_unit (List.map declared ~f:declaration) in
  let* () = Result.all_unit (List.map defined ~f:definition) in
  Ok defined

(** Logical definitions cannot depend on spatial resources. *)
let pure_logical_body env (t : S.term) =
  let bound = List.map env.vars ~f:fst in
  Result.all_unit
    (List.map (term_references bound t) ~f:(fun q ->
         if
           String.equal (qualid_key q) "own"
           || List.Assoc.mem env.ctx.given.preds (logical_key env q) ~equal:String.equal
         then
           error (S.qualid_loc q)
             "A pure logical function cannot use ownership or predicates"
         else Ok ()))

(** Nonrecursive logical definitions are checked with the rest of the proof. *)
let proof_function types ~shared ~ocaml_env ~preds ~spec_funcs ~proof_support ?member_name
    ~as_value declaration =
  match declaration with
  | S.Proof_function { function_name; function_params; function_result; function_body } ->
      let l = loc function_name.pid_loc in
      let ctx =
        spec_context types ~shared ~ocaml_env ~preds ~spec_funcs ~proof_support ()
      in
      State.in_procedure
      @@
      let open State.Syntax in
      let* params =
        State.all function_params ~f:(fun (id, ty) ->
            let* ty = State.of_result (Source.ocaml_type ocaml_env ~at:id.S.pid_loc ty) in
            let* raven_type = State.of_result (typ ctx ~at:id.pid_loc ty) in
            let+ raven = State.fresh id.pid_str in
            (id.pid_str, raven, ty, R.Var.make ~loc:l (ident ~loc:l raven) raven_type))
      in
      let* result_type =
        State.of_result
          (Source.ocaml_type ocaml_env ~at:function_name.pid_loc function_result)
      in
      let* result_type =
        State.of_result (typ ctx ~at:function_name.pid_loc result_type)
      in
      let env =
        {
          ctx;
          data = types;
          funcs = spec_funcs;
          logical_definition = true;
          vars = List.map params ~f:(fun (x, raven, _, _) -> (x, Raven raven));
          var_types = List.map params ~f:(fun (x, _, t, _) -> (x, t));
        }
      in
      let* () = State.of_result (pure_logical_body env function_body) in
      let* () =
        State.of_result
          (Source.check_logical_function ocaml_env ~functions:(List.map spec_funcs ~f:fst)
             declaration)
      in
      let* body = formula env function_body in
      let+ result = State.fresh "result" in
      let member =
        ident ~loc:l (Option.value member_name ~default:function_name.pid_str)
      in
      let body = R.Expr.annotated body result_type in
      if as_value then R.Member.value ~loc:l ~typ:result_type member (Some body)
      else
        R.Member.callable
          (R.Callable.func ~loc:l
             ~formals:(List.map params ~f:(fun (_, _, _, v) -> v))
             ~returns:[ R.Var.make ~loc:l (ident ~loc:l result) result_type ]
             member (Some body))
  | _ -> State.of_result (error Location.none "Expected a logical function declaration")

let scoped_contract_context types ~shared ~environment ~proof_support ~preds ~spec_funcs
    ~own_preds ~own_inputs () =
  let proof_support =
    { proof_support with predicate_inputs = own_inputs @ proof_support.predicate_inputs }
  in
  spec_context types ~shared ~ocaml_env:environment ~proof_support
    ~preds:(own_preds @ preds)
    ~spec_funcs:(List.map own_preds ~f:(fun (p, (raven, _)) -> (p, raven)) @ spec_funcs)
    ()

let check_adapter_shape ~at (contract : S.contract option) =
  match contract with
  | None -> Ok ()
  | Some c ->
      let ghost =
        Option.exists c.header ~f:(fun h ->
            List.exists (h.hd_args @ h.hd_ret) ~f:(function
              | S.Lghost _ -> true
              | _ -> false))
      in
      if ghost then
        unsupported at "Explicit ghost inputs or outputs in a checked module binding"
      else if c.pure || Option.is_some c.continues || not (List.is_empty c.variant) then
        unsupported at
          "A pure, continuation, or variant contract in a checked module binding"
      else if c.atomic && List.is_empty (c.atomic_requires @ c.atomic_ensures) then
        unsupported at "An atomic module contract without atomic clauses"
      else Ok ()

let logical_contract = function
  | None -> false
  | Some (c : S.contract) ->
      c.atomic || not (List.is_empty (c.atomic_requires @ c.atomic_ensures))

let generic_modules (source : Source.t) ~types ~functions inventory =
  let types =
    List.concat_map source.proof_resources ~f:(fun resource ->
        List.concat_map (resource :: Option.to_list resource.Source.resource_public)
          ~f:(fun resource ->
            resource.Source.resource_descriptor :: resource.resource_aliases))
    @ types
  in
  let groups =
    Generic_modules.plan
      ~proof_layout:(Generic_proofs.has_models source)
      inventory.Module_inventory.specializations
  in
  let annotations = Source.annotations source in
  let rec field_term (term : S.term) =
    match S.past_membership term with
    | Some (element, _, _) -> field_term element
    | None ->
        begin match term.term_desc with
        | Tfield _ -> true
        | Tapply (a, b) | Tinfix (a, _, b) | Tlet (_, a, b) ->
            field_term a || field_term b
        | Tif (a, b, c) -> field_term a || field_term b || field_term c
        | Tquant (_, _, t) | Tcomprehension (_, t) | Tattr (_, t) | Tcast (t, _) | Told t
          ->
            field_term t
        | Tmatch (t, cases) ->
            field_term t || List.exists cases ~f:(fun (_, t) -> field_term t)
        | Ttuple ts -> List.exists ts ~f:field_term
        | Trecord (base, fields) -> List.exists (S.record_terms base fields) ~f:field_term
        | Ttrue | Tfalse | Tconst _ | Tvar _ -> false
        end
  in
  let field_contract = function
    | None -> false
    | Some c ->
        List.exists
          (c.S.requires @ c.ensures @ c.atomic_requires @ c.atomic_ensures)
          ~f:field_term
  in
  let* groups =
    all groups ~f:(fun group ->
        let* modes =
          all group.applications ~f:(fun application ->
              all
                (List.zip_exn group.representative.parameters
                   application.source.parameters) ~f:(fun (representative, instance) ->
                  all
                    representative.Module_inventory.argument.expected.signature_resources
                    ~f:(fun (member, formal) ->
                      let actual =
                        List.Assoc.find_exn
                          instance.Module_inventory.argument.expected.signature_resources
                          member ~equal:String.equal
                      in
                      let* expected = implicit_parameters formal.declaration in
                      let* actual = implicit_parameters actual.declaration in
                      Ok (expected = actual))
                  |> Result.map ~f:(List.for_all ~f:Fn.id)))
        in
        let same_signature_sites application (function_ : func) =
          List.is_empty function_.signature_sites
          || List.exists group.representative.body_members
               ~f:(fun (name, representative_id) ->
                 Option.exists
                   (List.Assoc.find application.Generic_modules.source.body_members name
                      ~equal:String.equal)
                   ~f:(Ident.same function_.id)
                 && Option.exists
                      (List.find functions ~f:(fun representative ->
                           Ident.same representative.id representative_id))
                      ~f:(fun representative ->
                        List.equal
                          (fun (left : Module_inventory.signature_value)
                               (right : Module_inventory.signature_value) ->
                            Poly.equal left.declaration.val_loc right.declaration.val_loc)
                          function_.signature_sites representative.signature_sites))
        in
        let supported_functions =
          List.for_all group.applications ~f:(fun application ->
              List.for_all application.source.body_members ~f:(fun (_, id) ->
                  Option.exists
                    (List.find functions ~f:(fun f -> Ident.same f.id id))
                    ~f:(fun f ->
                      same_signature_sites application f
                      && (Option.is_some group.world || not (field_contract f.contract)))))
        in
        let* parameter_contracts =
          all
            (List.concat_map group.representative.parameters ~f:(fun instance ->
                 instance.Module_inventory.argument.expected.signature_values))
            ~f:(fun (_, signature) -> signature_contract signature)
        in
        let rec body_location (expression : Typedtree.module_expr) =
          match expression.mod_desc with
          | Tmod_functor (_, body) | Tmod_constraint (body, _, _, _) -> body_location body
          | _ -> expression.mod_loc
        in
        let body = body_location group.representative.template in
        let explicit_proofs =
          List.exists annotations ~f:(fun annotation ->
              let at = annotation.Annotation.loc in
              at.loc_start.pos_cnum >= body.loc_start.pos_cnum
              && at.loc_end.pos_cnum <= body.loc_end.pos_cnum
              &&
              match Annotation.kind annotation with
              | Contract | Manual | Scope | Ghost | Returns | Proof | Initially
              | Initializes | Linearization ->
                  false
              | _ -> true)
        in
        let representation_stable =
          List.for_all group.applications ~f:(fun application ->
              List.for_all application.source.parameters ~f:(fun instance ->
                  let concrete =
                    checked_raw_types types instance.Module_inventory.argument
                  in
                  List.for_all instance.argument.expected.signature_types
                    ~f:(fun (_, declaration) ->
                      Option.is_some declaration.Typedtree.typ_manifest
                      ||
                      let t =
                        Btype.newgenty
                          (Tconstr (Path.Pident declaration.typ_id, [], ref Types.Mnil))
                      in
                      match Datatypes.desc concrete t with
                      | Tconstr (path, _, _) ->
                          Option.exists (Datatypes.find concrete path) ~f:(fun data ->
                              Option.is_some data.Datatypes.library)
                      | _ -> false)))
        in
        Ok
          (Option.some_if
             (supported_functions && representation_stable && (not explicit_proofs)
             && (not (List.exists parameter_contracts ~f:field_contract))
             && List.for_all (List.concat modes) ~f:Fn.id)
             group))
  in
  let groups = List.filter_opt groups in
  Ok
    (List.filter groups ~f:(fun group ->
         Option.is_none group.Generic_modules.world
         || List.for_all group.applications ~f:(fun application ->
             List.for_all inventory.specializations ~f:(fun other ->
                 (not (Path.same application.source.identity other.identity))
                 || List.exists group.applications ~f:(fun member ->
                     phys_equal member.source other)))))

let scoped_predicate (binding : Proof_bindings.binding) =
  match binding.kind with
  | Predicate (p, definition) ->
      let p = { p with S.pred_name = { p.pred_name with pid_str = binding.backend } } in
      let definition =
        match definition with
        | Plain body -> if p.pred_persistent then Direct_invariant body else Body body
        | Stateful { state; fields; body; environment; state_scope } ->
            Invariant
              {
                state;
                fields;
                body;
                field_environment = environment;
                field_scope = Some state_scope;
              }
        | View value -> View { value }
      in
      Some (p.pred_name.pid_loc, p, definition, binding.private_types)
  | Lemma _ | Function _ | Resource _ | Field _ | Atomic _ | State _ | Action _ -> None

let scoped_lemma (binding : Proof_bindings.binding) =
  match binding.kind with
  | Predicate _ | Function _ | Resource _ | Field _ | Atomic _ | State _ | Action _ ->
      None
  | Lemma (S.Proof_lemma lemma) ->
      Some
        (S.Proof_lemma
           { lemma with lemma_name = { lemma.lemma_name with pid_str = binding.backend } })
  | Lemma _ -> None

let scoped_function (binding : Proof_bindings.binding) =
  match binding.kind with
  | Function (S.Proof_function declaration) ->
      Some
        (S.Proof_function
           {
             declaration with
             function_name = { declaration.function_name with pid_str = binding.backend };
           })
  | Predicate _ | Lemma _ | Function _ | Resource _ | Field _ | Atomic _ | State _
  | Action _ ->
      None

let check_scoped_resources ~types source inventory (proofs : Proof_bindings.t) =
  Result.all_unit
    (List.map inventory.Module_inventory.constraints ~f:(fun constraint_ ->
         match constraint_.owner with
         | None -> Ok ()
         | Some owner ->
             Result.all_unit
               (List.map constraint_.Module_inventory.signature.signature_resources
                  ~f:(fun (name, formal) ->
                    let* ( binding,
                           implementation_types,
                           implementation_environment,
                           check_projection ) =
                      match
                        List.find proofs.bindings ~f:(fun binding ->
                            Option.equal Path.same binding.entry.scope.owner (Some owner)
                            && String.equal binding.entry.name.pid_str name)
                      with
                      | Some binding ->
                          Ok
                            ( binding,
                              binding.private_types,
                              binding.environment,
                              Subst.identity )
                      | None ->
                          begin match
                            List.find proofs.applications ~f:(fun view ->
                                List.exists view.constraints ~f:(phys_equal constraint_)
                                && String.equal view.source.entry.name.pid_str name)
                          with
                          | Some view ->
                              Ok
                                ( view.source,
                                  view.implementation_types,
                                  view.environment,
                                  view.check_projection )
                          | None ->
                              error formal.site.item_loc
                                (Printf.sprintf
                                   "The module resource %s has no proof definition" name)
                          end
                    in
                    let* actual =
                      match binding.kind with
                      | Predicate (p, _) -> Ok p
                      | Lemma _ | Function _ | Resource _ | Field _ | Atomic _ | State _
                      | Action _ ->
                          error binding.entry.name.pid_loc
                            "A module resource must be defined as a predicate or \
                             invariant"
                    in
                    let declared = formal.declaration in
                    let* () =
                      if Option.is_none declared.pred_body then Ok ()
                      else
                        unsupported declared.pred_name.pid_loc
                          "A resource definition in a module signature"
                    in
                    let at = binding.entry.name.pid_loc in
                    let related =
                      [ (declared.pred_name.pid_loc, "Its signature declaration") ]
                    in
                    let* () =
                      if Bool.equal declared.pred_persistent actual.pred_persistent then
                        Ok ()
                      else
                        error at ~related
                          "The module resource has a different predicate or invariant \
                           kind"
                    in
                    let environment =
                      Source.annotation_env source formal.site.environment
                    in
                    let* raw =
                      all declared.pred_params ~f:(fun (id, ty) ->
                          Source.ocaml_type environment ~at:id.S.pid_loc ty)
                    in
                    let expected =
                      List.map raw ~f:(fun typ ->
                          Subst.type_expr check_projection
                            (Subst.type_expr constraint_.substitution typ))
                    in
                    let* equal =
                      Signature_contract.compiler ~at (fun () ->
                          List.length expected = List.length implementation_types
                          && Ctype.is_equal implementation_environment false expected
                               implementation_types)
                    in
                    let* () =
                      if equal then Ok ()
                      else
                        error at ~related
                          "The module resource has different parameter types"
                    in
                    let* expected = implicit_parameters declared in
                    let* actual_implicit = implicit_parameters actual in
                    if Int.equal expected actual_implicit then Ok ()
                    else
                      error at ~related
                        "The module resource has different implicit parameters"))))
