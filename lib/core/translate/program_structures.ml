(** The fourth phase of a program's translation: views and actions, shared structures and
    their applications, histories, facts about earlier states, and ghost arguments. *)

open Base
open Translate_context
open Atomic_proofs
open Procedures
open Program_items

type t = {
  structures : structure list;
  structure_member_lists : (structure * R.Member.t list) list;
  view_fields : (string * View_storage.t) list;
  shared : shared;
  generic_shared : (string * shared) list;
  past_structures : ?symbolic:bool -> Procedures.func -> structure list;
  pasts : (string * (string * string * int) list) list;
  past_returns : (string * past_return list) list;
  ghost_args : (string * (int * string) option list) list;
}

let destination_of_group = function
  | None -> Module_context.Flat
  | Some group -> Module_context.Worker group

let owner_destination ~(declaration_context : string -> Module_context.t) name =
  (declaration_context name).destination

let same_group left right =
  Module_context.same_destination (destination_of_group left) (destination_of_group right)

let field_group ~(generics : Generic_modules.t list) field =
  List.find generics ~f:(fun group ->
      String.is_prefix field ~prefix:(group.Generic_modules.name ^ "."))

let rec shared_for_destination ~(shared : shared)
    ~(generic_shared : (string * shared) list) = function
  | Module_context.Flat -> shared
  | Module_context.Worker group ->
      List.Assoc.find_exn generic_shared group.Generic_modules.name ~equal:String.equal
  | Module_context.Function_worker (_, parent) | Module_context.Proof_worker (_, parent)
    ->
      shared_for_destination ~shared ~generic_shared parent

let shared_for_proof ~(declaration_context : string -> Module_context.t)
    ~(shared : shared) ~(generic_shared : (string * shared) list) name =
  let owner_destination = owner_destination ~declaration_context in
  let shared_for_destination = shared_for_destination ~shared ~generic_shared in
  shared_for_destination (owner_destination name)

let body_shared ~(body_module_context : Procedures.func -> Module_context.t)
    ~(shared : shared) ~(generic_shared : (string * shared) list) f =
  let shared_for_destination = shared_for_destination ~shared ~generic_shared in
  shared_for_destination (body_module_context f).destination

let state_members ~destination_of destination lists =
  List.concat_map lists ~f:(fun (st, members) ->
      Option.some_if
        (Module_context.same_destination (destination_of st.invariant) destination)
        members
      |> Option.value ~default:[])

let run ~(history : History.encoding) (scopes : Program_scopes.t)
    (decls : Program_declarations.t) (proofs : Program_proofs.t) : (t, error) Result.t =
  let { Program_scopes.funcs; generic_proofs; generics; _ } = scopes in
  let declaration_context =
    Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
      ~unapplied_proofs:scopes.unapplied_proofs
  in
  let declaration_environment =
    Program_scopes.declaration_environment ~source:scopes.source
      ~unapplied_proofs:scopes.unapplied_proofs
  in
  let declaration_scope =
    Program_scopes.declaration_scope ~unapplied_proofs:scopes.unapplied_proofs
  in
  let proof_worker =
    Program_scopes.proof_worker ~module_contexts:scopes.module_contexts
      ~unapplied_proofs:scopes.unapplied_proofs
  in
  let { Program_declarations.predicates; scoped_proofs; source; types; _ } = decls in
  let generic key = Generic_parameters.find decls.generic_predicates key in
  let types_for key =
    Option.value_map (generic key) ~default:types ~f:(fun worker ->
        Generic_parameters.types worker types)
  in
  let predicate_backend key =
    match generic key with
    | Some worker -> worker.name ^ "." ^ Generic_parameters.member worker
    | None -> Module_context.member (declaration_context key) key
  in
  let view_backend key =
    match generic key with
    | Some worker -> worker.name ^ "." ^ view_field (Generic_parameters.member worker)
    | None -> Module_context.member (declaration_context key) (view_field key)
  in
  let body_module_context =
    Program_declarations.body_module_context ~module_contexts:scopes.module_contexts
      ~context_for_group:
        (Program_scopes.context_for_group ~module_contexts:scopes.module_contexts)
      ~generics:scopes.generics
  in
  let body_owner = Program_declarations.body_owner ~generics:scopes.generics in
  let body_proc_name =
    Program_declarations.body_proc_name ~generics:scopes.generics
      ~polymorphic_functions:decls.polymorphic_functions
      ~generic_procedures:decls.generic_procedures ~procedures:decls.procedures
  in
  let proc_name = Program_declarations.proc_name ~procedures:decls.procedures in
  let with_body_names lifted_argument =
    Program_declarations.with_body_names ~funcs:scopes.funcs ~procedures:decls.procedures
      ~polymorphic_functions:decls.polymorphic_functions ~generics:scopes.generics
      ~generic_procedures:decls.generic_procedures lifted_argument
  in
  let { Program_proofs.preds; proof_support; spec_funcs; _ } = proofs in
  let module_context =
    Program_proofs.module_context
      ~scoped_binding:
        (Program_scopes.scoped_binding ~unapplied_proofs:scopes.unapplied_proofs)
      ~module_parameters:proofs.module_parameters
  in
  let proof_context = Program_proofs.proof_context proofs.proof_env in
  let proof_context_for =
    Program_proofs.proof_context_for proofs.proof_env
      ~declaration_context:
        (Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
           ~unapplied_proofs:scopes.unapplied_proofs)
      ~declaration_scope:
        (Program_scopes.declaration_scope ~unapplied_proofs:scopes.unapplied_proofs)
      ~scoped_binding:
        (Program_scopes.scoped_binding ~unapplied_proofs:scopes.unapplied_proofs)
      ~module_parameters:proofs.module_parameters
  in
  (* The views, with their values, and their ghost fields, on the structures. *)
  let views =
    List.filter_map predicates ~f:(fun (_, p, def, types) ->
        match def with
        | View { value } -> Some (p, value, types)
        | Body _ | Direct_invariant _ | Invariant _ -> None)
  in
  let* view_fields =
    all views ~f:(fun ((p : S.predicate), _, param_types) ->
        let types = types_for p.pred_name.pid_str in
        let at = p.pred_name.pid_loc in
        let structure = List.hd_exn param_types in
        let* allocation =
          match Option.map (anchor types structure) ~f:fst with
          | Some tag -> Ok tag
          | None ->
              error at
                "The structure of a view is a reference: an atomic, a ref or a record \
                 with a mutable field"
        in
        let* typ = Datatypes.typ types ~at (List.last_exn param_types) in
        let field = view_backend p.pred_name.pid_str in
        Ok (allocation, { View_storage.field; value_type = typ }))
  in
  let resolve_function ~environment (id : S.id) =
    match Source.value_path environment (S.Qid id) with
    | Some path ->
        let path = Proof_bindings.canonical_owner scoped_proofs path in
        begin match
          List.find funcs ~f:(fun f -> List.mem f.paths path ~equal:Path.same)
        with
        | Some f -> Ok f.id
        | None ->
            begin match
              List.find_map generic_proofs ~f:(fun plan ->
                  Generic_proofs.function_id plan path)
            with
            | Some id -> Ok id
            | None ->
                error id.pid_loc
                  (Printf.sprintf "There is no implementation function %s" id.pid_str)
            end
        end
    | None ->
        error id.pid_loc
          (Printf.sprintf "There is no implementation function %s" id.pid_str)
  in
  (* The structures with a state, and their histories, allocated empty. *)
  let action_declarations =
    List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
        match entry.Proof_scopes.declaration with
        | S.Proof_action declaration ->
            let scope = Option.some_if (Option.is_some entry.scope.owner) entry.scope in
            let backend =
              Option.value_map
                (List.find scoped_proofs.bindings ~f:(fun binding ->
                     Ident.same binding.entry.id entry.id))
                ~default:declaration.action_name.pid_str
                ~f:(fun binding -> binding.backend)
            in
            Some
              ( scope,
                Source.annotation_env source entry.scope.environment,
                backend,
                entry.declaration )
        | _ -> None)
  in
  let* actions =
    all action_declarations ~f:(fun (scope, environment, backend, proof) ->
        match proof with
        | S.Proof_action declaration ->
            let* linearizes =
              all declaration.action_linearizes ~f:(resolve_function ~environment)
            in
            let helps =
              Option.bind declaration.action_helps ~f:(fun (field, key, result) ->
                  match field.term_desc with
                  | Tfield (_, Qid field) -> Some (field.pid_str, key, result)
                  | _ -> None)
            in
            Ok
              ( scope,
                {
                  action = backend;
                  params = List.map declaration.action_params ~f:(fun id -> id.S.pid_str);
                  step =
                    Option.map declaration.action_step ~f:(fun (op, args) ->
                        (op.pid_str, args));
                  state = declaration.action_state.pid_str;
                  update =
                    List.map declaration.action_update ~f:(fun (field, term) ->
                        (field.S.pid_str, term));
                  linearizes;
                  helps;
                  action_at = declaration.action_name.pid_loc;
                } )
        | _ -> error Location.none "Expected an action declaration")
  in
  let same_scope a b =
    Option.equal
      (fun a b -> Option.equal Path.same a.Proof_scopes.owner b.Proof_scopes.owner)
      a b
  in
  let* structures =
    all
      (List.filter_map predicates ~f:(fun (at, p, def, param_types) ->
           match def with
           | Invariant
               { state; fields; field_types; body; field_environment; field_scope; _ } ->
               Some
                 ( at,
                   p,
                   state,
                   fields,
                   field_types,
                   body,
                   param_types,
                   field_environment,
                   field_scope )
           | Body _ | Direct_invariant _ | View _ -> None))
      ~f:(fun
          ( at,
            (p : S.predicate),
            state,
            state_fields,
            state_types,
            body,
            param_types,
            field_environment,
            field_scope )
        ->
        let types = types_for p.pred_name.pid_str in
        let scope = declaration_scope p.pred_name.pid_str in
        let environment = declaration_environment p.pred_name.pid_str in
        let declaration_predicates, declaration_functions, declaration_support =
          proof_context_for ~preds ~spec_funcs ~proof_support p.pred_name.pid_str
        in
        let context =
          {
            declaration_predicates =
              List.map declaration_predicates ~f:(fun (key, (target, parameters)) ->
                  ( key,
                    match generic key with
                    | Some worker ->
                        ( worker.name ^ "." ^ Generic_parameters.member worker,
                          if
                            Option.exists (generic p.pred_name.pid_str) ~f:(fun owner ->
                                String.equal owner.name worker.name)
                          then worker.parameters
                          else parameters )
                    | None -> (target, parameters) ));
            declaration_functions;
            declaration_support;
          }
        in
        let state_types =
          let private_state =
            match (field_scope, scope) with
            | None, _ -> true
            | Some owner, Some caller ->
                Option.is_some
                  (Proof_bindings.drop_prefix owner.namespace caller.namespace)
            | Some _, None -> false
          in
          if private_state then state_types
          else
            let project ty =
              Proof_bindings.context_type scoped_proofs ~environment
                (Proof_bindings.public_type scoped_proofs ty)
            in
            match generic p.pred_name.pid_str with
            | None -> Compiler_types.map_group state_types ~f:project
            | Some worker ->
                let projected =
                  Compiler_types.map_group (worker.variables @ state_types) ~f:project
                in
                let variables, parameters =
                  List.split_n projected (List.length worker.variables)
                in
                Generic_parameters.parameter_types
                  { worker with variables; parameters }
                  worker.variables
        in
        let typed_fields = List.zip_exn state_fields state_types in
        let actions =
          List.filter_map actions ~f:(fun (owner, action) ->
              Option.some_if
                (same_scope owner scope
                && String.equal action.state state
                && List.for_all action.update ~f:(fun (field, _) ->
                    List.exists state_fields ~f:(fun sf ->
                        String.equal sf.S.sf_name.pid_str field)))
                action)
        in
        (* The key type of a field of pending calls. *)
        let pending_key t =
          match Datatypes.desc types t with
          | Tconstr (path, [ key ], _) when Path.same path source.pending -> Some key
          | _ -> None
        in
        let* fields =
          all typed_fields ~f:(fun ((sf : S.state_field), t) ->
              let raven = state ^ "_" ^ sf.sf_name.pid_str in
              match pending_key t with
              | Some _ ->
                  (* The registrations, which only grow. *)
                  Ok
                    ( sf.sf_name.pid_str,
                      raven,
                      R.Type.fin_set ~loc:(loc at) (R.Type.ref ~loc:(loc at)),
                      t,
                      true )
              | None ->
                  let* typ = Datatypes.typ types ~at t in
                  Ok (sf.sf_name.pid_str, raven, typ, t, sf.sf_grows))
        in
        let* pendings =
          all
            (List.filter_map typed_fields ~f:(fun ((sf : S.state_field), t) ->
                 Option.map (pending_key t) ~f:(fun key -> (sf, key))))
            ~f:(fun ((sf : S.state_field), key) ->
              let field = sf.sf_name.pid_str in
              let* helped =
                match sf.sf_helps with
                | Some f ->
                    resolve_function ~environment:field_environment
                      (S.mk_id ~loc:sf.sf_name.pid_loc f)
                | None ->
                    error sf.sf_name.pid_loc
                      "A field of pending calls names the function whose calls wait, as \
                       [@helps is_empty]"
              in
              let* helping =
                match
                  List.filter_map actions ~f:(fun a ->
                      match a.helps with
                      | Some (f, k, v) when String.equal f field -> Some (a.state, k, v)
                      | _ -> None)
                with
                | [ helping ] -> Ok helping
                | [] ->
                    error sf.sf_name.pid_loc
                      "No action helps the calls of this field: give one as [helps s.f \
                       on key with result]"
                | _ :: _ :: _ ->
                    unsupported sf.sf_name.pid_loc
                      "Helping the calls of a field by several actions"
              in
              Ok
                {
                  pending_field = field;
                  pending_on = state ^ "_" ^ field ^ "_on";
                  key_type = key;
                  helped;
                  helping;
                })
        in
        let chains =
          List.dedup_and_sort ~compare:String.compare
            (List.filter_map (conjuncts body) ~f:(fun t ->
                 Option.map (chain_of ~state t) ~f:(fun (_, _, field, _) -> field)))
        in
        let st =
          {
            generic = generic p.pred_name.pid_str;
            context;
            scope;
            environment;
            invariant = p.pred_name.pid_str;
            backend = predicate_backend p.pred_name.pid_str;
            state;
            fields;
            chains = List.map chains ~f:(fun f -> (f, state ^ "_" ^ f ^ "_index"));
            actions;
            pendings;
            held =
              List.filter_map (conjuncts body) ~f:(fun t ->
                  match spine t [] with
                  | ( { term_desc = Tvar (Qid { pid_str = "own"; _ }); _ },
                      [ location; value ] ) ->
                      begin match spine value [] with
                      | ( { term_desc = Tvar (Qid { pid_str = "([])"; _ }); _ },
                          [
                            {
                              term_desc =
                                Tfield
                                  ( { term_desc = Tvar (Qid { pid_str = x; _ }); _ },
                                    Qid { pid_str = f; _ } );
                              _;
                            };
                            position;
                          ] )
                        when String.equal x state && List.mem chains f ~equal:String.equal
                        ->
                          Some (location, f, position)
                      | _ -> None
                      end
                  | _ -> None);
            params =
              List.zip_exn
                (List.map p.pred_params ~f:(fun (x, _) -> x.S.pid_str))
                (List.take param_types (List.length p.pred_params));
            structure_type = List.hd_exn param_types;
            views =
              List.filter_map views ~f:(fun (view, value, view_types) ->
                  Option.some_if
                    (List.mem
                       (Program_declarations.view_owners ~scope_of:declaration_scope
                          ~environment predicates (view, value, view_types))
                       p.pred_name.pid_str ~equal:String.equal)
                    (view, value));
            parts = [];
            at;
          }
        in
        Ok { st with parts = invariant_parts types st body })
  in
  let* _ =
    all actions ~f:(fun (_, action) ->
        match
          List.filter structures ~f:(fun st ->
              List.exists st.actions ~f:(fun a -> String.equal a.action action.action))
        with
        | [ _ ] -> Ok ()
        | [] -> error action.action_at "No stateful invariant matches this action"
        | _ ->
            error action.action_at
              "Several stateful invariants match this action: use distinct state binders")
  in
  let* _ =
    all views ~f:(fun (view, _, _) ->
        match
          List.filter structures ~f:(fun st ->
              List.exists st.views ~f:(fun (p, _) ->
                  String.equal p.S.pred_name.pid_str view.S.pred_name.pid_str))
        with
        | [ _ ] -> Ok ()
        | [] -> error view.pred_name.pid_loc "No stateful invariant matches this view"
        | _ ->
            error view.pred_name.pid_loc
              "Several stateful invariants match this view: use distinct state binders")
  in
  let* application_identities =
    all generics ~f:(fun group ->
        let* identities =
          all group.Generic_modules.applications ~f:(fun application ->
              let* identity =
                Signature_contract.compiler ~at:application.source.argument.site.item_loc
                  (fun () ->
                    Env.normalize_module_path None source.env application.source.identity)
              in
              Ok (application, identity))
        in
        Ok (group.name, identities))
  in
  let canonical_application group application =
    let identities =
      List.Assoc.find_exn application_identities group.Generic_modules.name
        ~equal:String.equal
    in
    let identity = List.Assoc.find_exn identities application ~equal:phys_equal in
    fst (List.find_exn identities ~f:(fun (_, other) -> Path.same other identity))
  in
  let application_aliases =
    List.concat_map generics ~f:(fun group ->
        List.filter_map group.Generic_modules.applications ~f:(fun application ->
            let canonical = canonical_application group application in
            Option.some_if
              (not (phys_equal canonical application))
              (application.name, canonical.name)))
  in
  let canonical_backend backend =
    Option.value
      (List.find_map application_aliases ~f:(fun (alias, target) ->
           Option.map
             (String.chop_prefix backend ~prefix:(alias ^ "."))
             ~f:(fun suffix -> target ^ "." ^ suffix)))
      ~default:backend
  in
  let declared_structures = structures in
  let* application_structures =
    all
      (List.filter_map scoped_proofs.applications ~f:(fun view ->
           Option.map
             (List.find structures ~f:(fun st ->
                  String.equal st.invariant view.source.backend))
             ~f:(fun st -> (view, st))))
      ~f:(fun (view, st) ->
        let plan = Option.value_exn (proof_worker st.invariant) in
        let applied_generic =
          Option.map (generic view.Proof_bindings.key) ~f:(fun worker ->
              { worker with name = canonical_backend worker.name })
        in
        let types =
          Option.value_map applied_generic ~default:types ~f:(fun worker ->
              Generic_parameters.types worker types)
        in
        let project ty =
          match (st.generic, applied_generic) with
          | Some original, Some applied ->
              let packed = Generic_parameters.aggregate (original.variables @ [ ty ]) in
              let projected = view.project_type packed in
              let components =
                match Types.get_desc projected with
                | Ttuple fields -> List.map fields ~f:snd
                | _ -> [ projected ]
              in
              let variables, values =
                List.split_n components (List.length original.variables)
              in
              List.hd_exn
                (Generic_parameters.parameter_types
                   { original with variables; parameters = values }
                   applied.variables)
          | _ -> view.project_type ty
        in
        let rebase text =
          Option.value_map
            (String.chop_prefix text ~prefix:(plan.group.name ^ "."))
            ~default:text
            ~f:(fun suffix ->
              let prefix = (Qualified_name.of_string view.backend).path in
              canonical_backend (String.concat ~sep:"." (prefix @ [ suffix ])))
        in
        let instance =
          List.find_exn plan.group.applications ~f:(fun instance ->
              String.equal view.backend
                (instance.Generic_modules.name ^ "." ^ view.source.backend))
        in
        let projection =
          Generic_proofs.application_projection source plan instance.source view.path
        in
        let project_path = Subst.module_path projection in
        let project_atomic_source (au : Source.proof_au) =
          {
            au with
            au_scope = Option.map au.au_scope ~f:project_path;
            au_path = project_path au.au_path;
            au_operation_path = project_path au.au_operation_path;
            au_token_path = project_path au.au_token_path;
            au_token_paths = List.map au.au_token_paths ~f:project_path;
          }
        in
        let project_lemma signature =
          {
            signature with
            lemma_raven = rebase signature.lemma_raven;
            lemma_inputs = List.map signature.lemma_inputs ~f:project;
            lemma_outputs = List.map signature.lemma_outputs ~f:project;
          }
        in
        let support = st.context.declaration_support in
        let support =
          {
            support with
            runtime_functions =
              Path_bindings.of_list
                (List.map support.runtime_functions.entries ~f:(fun (path, target) ->
                     ( project_path path,
                       Qualified_name.of_string (rebase (Qualified_name.to_string target))
                     )));
            predicate_views =
              Path_bindings.of_list
                (List.map support.predicate_views.entries ~f:(fun (path, key) ->
                     (project_path path, rebase key)));
            public_types = List.map support.public_types ~f:project_path;
            library_paths =
              Path_bindings.of_list
                (List.map support.library_paths.entries ~f:(fun (path, names) ->
                     (project_path path, names)));
            resources =
              List.map support.resources ~f:(fun resource ->
                  let resource = Source.map_resource_types resource ~f:project in
                  {
                    resource with
                    resource_backend = rebase resource.Source.resource_backend;
                    resource_path = project_path resource.resource_path;
                  });
            ghost_fields =
              List.map support.ghost_fields ~f:(fun field ->
                  let field = Source.map_field_types field ~f:project in
                  {
                    field with
                    field_backend = rebase field.Source.field_backend;
                    field_scope = Option.map field.field_scope ~f:project_path;
                    field_path = project_path field.field_path;
                    field_resource = Option.map field.field_resource ~f:project_path;
                  });
            atomic_updates =
              List.map support.atomic_updates ~f:(fun signature ->
                  let signature = map_atomic_types signature ~f:project in
                  {
                    signature with
                    au_owner = Option.map signature.au_owner ~f:project_path;
                    au_source = project_atomic_source signature.au_source;
                    au_generic =
                      Option.map signature.au_generic ~f:(fun generic ->
                          { generic with name = rebase generic.name });
                    au_procedure = rebase signature.au_procedure;
                  });
            logical_functions =
              List.map support.logical_functions ~f:(fun (key, signature) ->
                  (key, project_lemma signature));
          }
        in
        let* fields =
          all st.fields ~f:(fun (field, raven, typ, ty, grows) ->
              let ty = project ty in
              let* typ =
                if
                  List.exists st.pendings ~f:(fun pending ->
                      String.equal pending.pending_field field)
                then Ok typ
                else Datatypes.typ types ~at:st.at ty
              in
              Ok (field, raven, typ, ty, grows))
        in
        let views =
          List.filter_map st.views ~f:(fun (predicate, value) ->
              Option.map
                (List.find scoped_proofs.applications ~f:(fun other ->
                     Path.same other.path view.path
                     && String.equal other.source.backend predicate.S.pred_name.pid_str))
                ~f:(fun other ->
                  ( {
                      predicate with
                      pred_name = { predicate.pred_name with pid_str = other.key };
                    },
                    value )))
        in
        let member_id id =
          Option.value_map
            (List.find plan.group.representative.body_members ~f:(fun (_, original) ->
                 Ident.same original id))
            ~default:id
            ~f:(fun (name, _) ->
              Option.value
                (List.Assoc.find instance.source.body_members name ~equal:String.equal)
                ~default:id)
        in
        let application_substitution =
          Generic_proofs.application_substitution plan instance.source
        in
        let environment =
          List.fold (Generic_proofs.source_parameters plan) ~init:view.environment
            ~f:(fun environment parameter ->
              let argument =
                Subst.module_path application_substitution (Path.Pident parameter)
              in
              Env.add_module ~noalias:false parameter Types.Mp_present
                (Types.Mty_alias argument) environment)
        in
        let projected_predicates =
          List.map st.context.declaration_predicates ~f:(fun (key, (target, tys)) ->
              (key, (rebase target, Compiler_types.map_group tys ~f:project)))
        in
        let application_predicates =
          List.filter_map scoped_proofs.applications ~f:(fun other ->
              if Path.same other.path view.path then
                Option.map
                  (List.Assoc.find projected_predicates other.source.backend
                     ~equal:String.equal) ~f:(fun signature -> (other.key, signature))
              else None)
        in
        Ok
          {
            st with
            generic = applied_generic;
            invariant = rebase st.backend;
            backend = rebase st.backend;
            fields;
            views;
            environment;
            context =
              {
                declaration_predicates = application_predicates @ projected_predicates;
                declaration_functions =
                  List.map st.context.declaration_functions ~f:(fun (key, target) ->
                      (key, rebase target));
                declaration_support = support;
              };
            params = List.map st.params ~f:(fun (key, ty) -> (key, project ty));
            structure_type = project st.structure_type;
            actions =
              List.map st.actions ~f:(fun action ->
                  { action with linearizes = List.map action.linearizes ~f:member_id });
            pendings =
              List.map st.pendings ~f:(fun pending ->
                  {
                    pending with
                    key_type = project pending.key_type;
                    helped = member_id pending.helped;
                  });
          })
  in
  let application_structures =
    List.dedup_and_sort application_structures ~compare:(fun left right ->
        String.compare left.backend right.backend)
  in
  let* structure_member_lists =
    all structures ~f:(fun st ->
        let* members = structure_members ~history (types_for st.invariant) st ~at:st.at in
        Ok (st, members))
  in
  let history_fields =
    List.map (List.filter structures ~f:has_history) ~f:(fun st ->
        let tag =
          Option.value_map
            (anchor (types_for st.invariant) st.structure_type)
            ~default:"" ~f:fst
        in
        let l = R.Loc.none in
        ( tag,
          (member_name st "history", Fixed (history_elements ~loc:l history st).initial)
        ))
  in
  let allocated_fields =
    List.map view_fields ~f:(fun (anchor, view) ->
        (anchor, (view.View_storage.field, Snapshot view.value_type)))
    @ history_fields
  in
  let owner_destination = owner_destination ~declaration_context in
  let visible_state group name =
    match owner_destination name with
    | Module_context.Flat -> true
    | destination ->
        Module_context.same_destination destination (destination_of_group group)
  in
  let field_group = field_group ~generics in
  let make_shared group =
    let persistent =
      List.concat_map predicates ~f:(fun (at, p, def, _) ->
          match def with
          | (Direct_invariant _ | Invariant _)
            when visible_state group p.pred_name.pid_str ->
              let key = p.pred_name.pid_str in
              (predicate_backend key, at)
              ::
              (if Option.is_none (generic key) then []
               else
                 [ (key, at); (Module_context.member (declaration_context key) key, at) ])
          | Body _ | Direct_invariant _ | Invariant _ | View _ -> [])
    in
    let selected_views =
      List.filter views ~f:(fun (p, _, _) -> visible_state group p.S.pred_name.pid_str)
    in
    let view_names =
      List.map selected_views ~f:(fun (p, _, _) ->
          let key = p.S.pred_name.pid_str in
          let field = view_backend key in
          (key, field))
    in
    let persistent, view_names =
      match group with
      | Some _ -> (persistent, view_names)
      | None ->
          List.fold scoped_proofs.applications ~init:(persistent, view_names)
            ~f:(fun (persistent, views) view ->
              match view.source.kind with
              | Predicate (p, View _) ->
                  let backend = Qualified_name.of_string view.backend in
                  ( persistent,
                    ( view.key,
                      match generic view.key with
                      | Some worker ->
                          canonical_backend
                            (worker.name ^ "."
                            ^ view_field (Generic_parameters.member worker))
                      | None ->
                          canonical_backend
                            (String.concat ~sep:"."
                               (backend.path @ [ view_field backend.name ])) )
                    :: views )
              | Predicate (p, _) when p.pred_persistent ->
                  ( ( (match generic view.key with
                      | Some worker ->
                          canonical_backend
                            (worker.name ^ "." ^ Generic_parameters.member worker)
                      | None -> canonical_backend view.backend),
                      p.pred_name.pid_loc )
                    :: (view.backend, p.pred_name.pid_loc)
                    :: persistent,
                    views )
              | _ -> (persistent, views))
    in
    let selected_fields =
      List.filter allocated_fields ~f:(fun (_, (field, _)) ->
          let generic_template =
            List.exists decls.generic_predicate_workers ~f:(fun worker ->
                String.is_prefix field ~prefix:(worker.Generic_parameters.name ^ "."))
          in
          (not generic_template)
          &&
          match field_group field with
          | None -> true
          | Some owner -> Option.exists group ~f:(phys_equal owner))
    in
    {
      persistent;
      member_aliases = (if Option.is_none group then application_aliases else []);
      history;
      views = view_names;
      structures =
        (List.filter_map declared_structures ~f:(fun st ->
             Option.some_if
               (visible_state group st.invariant)
               { st with invariant = st.backend })
        @ if Option.is_none group then application_structures else []);
      anchors =
        List.map
          (List.dedup_and_sort (List.map selected_fields ~f:fst) ~compare:String.compare)
          ~f:(fun anchor ->
            ( anchor,
              List.filter_map selected_fields ~f:(fun (owner, field) ->
                  Option.some_if (String.equal owner anchor) field) ));
    }
  in
  let shared = make_shared None in
  let generic_shared =
    List.map generics ~f:(fun group ->
        (group.Generic_modules.name, make_shared (Some group)))
  in
  let body_shared = body_shared ~body_module_context ~shared ~generic_shared in
  let past_structures ?(symbolic = false) (f : func) =
    let scope = Proof_bindings.scope_for_location scoped_proofs f.loc in
    let context = proof_context scope preds spec_funcs proof_support in
    let owner = body_module_context f in
    let predicates, _, support =
      module_context owner
        ~projection:(Program_declarations.source_function_projection ~generics owner f)
        context
    in
    let selected_shared = if symbolic then body_shared f else shared in
    let project_backend backend =
      match (symbolic, body_owner f) with
      | false, Some (group, _) ->
          let _, application, _ =
            Option.value_exn (Generic_modules.member generics f.id)
          in
          let target = (canonical_application group application).name in
          Option.value_map
            (String.chop_prefix backend ~prefix:(group.name ^ "."))
            ~default:backend
            ~f:(fun suffix -> target ^ "." ^ suffix)
      | _ -> backend
    in
    let predicate_target key backend =
      (match generic key with
        | Some worker -> worker.name ^ "." ^ Generic_parameters.member worker
        | None -> backend)
      |> project_backend
      |> canonical_member selected_shared
    in
    let structures = selected_shared.structures in
    let references =
      Option.value_map f.contract ~default:[] ~f:(fun c ->
          List.concat_map (c.requires @ c.ensures) ~f:(term_references []))
    in
    let keys =
      List.filter_map references ~f:(fun q ->
          let key =
            match (support.proof_key f.environment q, q) with
            | Some key, _ -> Some key
            | None, S.Qid id -> Some id.pid_str
            | None, Qdot _ -> None
          in
          Option.map key ~f:(fun key ->
              Option.value_map (List.Assoc.find predicates key ~equal:String.equal)
                ~default:key ~f:(fun (backend, _) -> predicate_target key backend)))
    in
    let selected =
      List.filter structures ~f:(fun st ->
          List.mem keys st.invariant ~equal:String.equal
          || List.exists st.views ~f:(fun (p, _) ->
              List.mem keys
                (Option.value_map
                   (List.Assoc.find predicates p.S.pred_name.pid_str ~equal:String.equal)
                   ~default:p.pred_name.pid_str ~f:(fun (backend, _) ->
                     predicate_target p.pred_name.pid_str backend))
                ~equal:String.equal))
    in
    if not (List.is_empty selected) then selected
    else
      let namespace =
        Option.value_map scope ~default:[] ~f:(fun s -> s.Proof_scopes.namespace)
      in
      let owner st =
        Option.value_map st.scope ~default:[] ~f:(fun s -> s.Proof_scopes.namespace)
      in
      let visible =
        List.filter structures ~f:(fun st ->
            Option.is_some (Proof_bindings.drop_prefix (owner st) namespace))
      in
      List.filter visible ~f:(fun st ->
          not
            (List.exists visible ~f:(fun other ->
                 String.equal st.state other.state
                 && List.length (owner other) > List.length (owner st))))
  in
  (* The facts about earlier states in contracts, by the parameter they are about. *)
  let* pasts =
    all funcs ~f:(fun f ->
        let structures = past_structures f in
        let* _ =
          all
            (Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires @ c.ensures))
            ~f:(fun term ->
              if
                List.count structures ~f:(fun st -> Option.is_some (past_of [ st ] term))
                > 1
              then
                error term.term_loc
                  "Several stateful invariants match this past fact: use distinct state \
                   binders"
              else Ok ())
        in
        let clauses select =
          Option.value_map f.contract ~default:[] ~f:select
          |> List.filter_map ~f:(past_of structures)
        in
        let* _, names =
          contract_names f
            (Option.bind f.contract ~f:(fun c -> c.header))
            (List.length f.params)
        in
        let* required =
          all
            (clauses (fun c -> c.requires))
            ~f:(fun p ->
              let position =
                match p.element.term_desc with
                | Tvar (Qid { pid_str = x; _ }) ->
                    List.findi names ~f:(fun _ n -> Option.equal String.equal n (Some x))
                | _ -> None
              in
              match position with
              | Some (i, _) -> Ok (p.inv, p.field, i)
              | None ->
                  unsupported p.element.term_loc
                    "A fact about an earlier state other than of a parameter,")
        in
        let* returned =
          match clauses (fun c -> c.ensures) with
          | [] -> Ok []
          | clauses ->
              let scope = Proof_bindings.scope_for_location scoped_proofs f.loc in
              let context = proof_context scope preds spec_funcs proof_support in
              let owner = body_module_context f in
              let preds, spec_funcs, proof_support =
                module_context owner
                  ~projection:
                    (Program_declarations.source_function_projection ~generics owner f)
                  context
              in
              let* scheme =
                Polymorphic_functions.discover
                  ~additional:(Program_declarations.parameter_types f)
                  ~expand:(Datatypes.expand types) ~at:f.loc f.scheme_type
              in
              (* Application contracts are checked even when their body is shared. *)
              let contract_types =
                List.mapi scheme.variables ~f:(fun index variable ->
                    Datatypes.variable_type ~variable
                      ~owner:(String.split (proc_name f) ~on:'.')
                      ~parameter:("A" ^ Int.to_string index)
                      ~at:f.loc)
                @ types
              in
              let ctx =
                Proof_declarations.spec_context contract_types ~shared:(body_shared f)
                  ~ocaml_env:f.environment ~preds ~spec_funcs ~proof_support
                  ~generic_predicates:decls.generic_predicates ()
              in
              let computation =
                let open State.Syntax in
                let* formals = formals ~names ctx f in
                let typed_function =
                  {
                    f with
                    contract =
                      Option.map f.contract ~f:(fun contract ->
                          let ordinary terms =
                            List.filter terms ~f:(fun term ->
                                Option.is_none (past_of structures term))
                          in
                          {
                            contract with
                            requires = ordinary contract.requires;
                            ensures = ordinary contract.ensures;
                          });
                  }
                in
                let* _, env, _, _ =
                  contract_env ctx ~spec_funcs typed_function formals
                    ~result:"past$result"
                in
                State.all clauses ~f:(fun p ->
                    let+ past_element =
                      State.of_result
                        (match Spec_terms.term_type env p.element with
                        | Some typ -> Ok typ
                        | None ->
                            Source.infer_logical_expression f.environment
                              ~functions:(List.map env.funcs ~f:fst)
                              ~variables:(Logical_context.variables env)
                              p.element)
                    in
                    {
                      past_invariant = p.inv;
                      past_field = p.field;
                      past_entry = entry_of_args types f names p.element;
                      past_inputs =
                        List.map f.params ~f:(fun parameter ->
                            match parameter.Typedtree.fp_kind with
                            | Tparam_pat pattern | Tparam_optional_default (pattern, _) ->
                                pattern.pat_type);
                      past_result = f.body.exp_type;
                      past_element;
                    })
              in
              let* result, _ = State.run_from State.initial computation in
              Ok result
        in
        Ok ((proc_name f, required), (proc_name f, returned)))
  in
  let pasts, past_returns = List.unzip pasts in
  let body_past_name f inv =
    match body_owner f with
    | None -> inv
    | Some (group, _) ->
        let _, application, _ = Option.value_exn (Generic_modules.member generics f.id) in
        let prefix = (canonical_application group application).name in
        Option.value_map
          (String.chop_prefix inv ~prefix:(prefix ^ "."))
          ~default:inv
          ~f:(fun suffix -> group.name ^ "." ^ suffix)
  in
  let with_body_pasts entries project =
    entries
    @ List.filter_map funcs ~f:(fun f ->
        match body_owner f with
        | (Some (_, true) | None) when not (String.equal (proc_name f) (body_proc_name f))
          ->
            Option.map
              (List.Assoc.find entries (proc_name f) ~equal:String.equal)
              ~f:(fun value -> (body_proc_name f, project f value))
        | Some _ | None -> None)
  in
  let pasts =
    with_body_pasts pasts (fun f clauses ->
        List.map clauses ~f:(fun (inv, field, position) ->
            (body_past_name f inv, field, position)))
  in
  let past_returns =
    with_body_pasts past_returns (fun f clauses ->
        List.map clauses ~f:(fun past ->
            { past with past_invariant = body_past_name f past.past_invariant }))
  in
  (* For each ghost parameter, a parameter that a precondition makes a field of it. *)
  let* ghost_args =
    all funcs ~f:(fun f ->
        let* _, names =
          contract_names f
            (Option.bind f.contract ~f:(fun c -> c.header))
            (List.length f.params)
        in
        let equations =
          field_equations
            (Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires))
        in
        Ok
          ( proc_name f,
            List.map (ghost_params f) ~f:(fun (g, _) ->
                List.find_map equations ~f:(fun (x, field, h) ->
                    if not (String.equal h g.S.pid_str) then None
                    else
                      Option.map
                        (List.findi names ~f:(fun _ n ->
                             Option.equal String.equal n (Some x)))
                        ~f:(fun (i, _) -> (i, field)))) ))
  in
  let ghost_args = with_body_names ghost_args in
  Ok
    {
      structures;
      structure_member_lists;
      view_fields;
      shared;
      generic_shared;
      past_structures;
      pasts;
      past_returns;
      ghost_args;
    }
