(** Source dependencies between dictionary-indexed declaration workers. *)

open Base
module S = Caravan_spec.Spec_ast

type t = { families : Generic_families.t }

let contract_terms (contract : S.contract) =
  contract.requires @ contract.ensures @ contract.atomic_requires
  @ contract.atomic_ensures @ contract.variant

let rec proof_references bound (expression : S.proof_expr) =
  let term = Translate_context.term_references bound in
  let proof = proof_references bound in
  match expression.proof_desc with
  | Proof_value value | Proof_assert value | Proof_unfold (value, _) -> term value
  | Proof_fold (value, witnesses) ->
      term value @ List.concat_map witnesses ~f:(fun (_, value) -> term value)
  | Proof_let (pattern, value, body) ->
      proof value @ proof_references (Translate_context.pat_names pattern @ bound) body
  | Proof_seq (left, right) -> proof left @ proof right
  | Proof_if (condition, left, right) -> term condition @ proof left @ proof right
  | Proof_match (value, cases) ->
      term value
      @ List.concat_map cases ~f:(fun (pattern, body) ->
          proof_references (Translate_context.pat_names pattern @ bound) body)

let declaration_references = function
  | S.Proof_predicate predicate ->
      Option.value_map predicate.pred_body ~default:[]
        ~f:
          (Translate_context.term_references
             (List.map predicate.pred_params ~f:(fun (id, _) -> id.S.pid_str)))
  | Proof_function { function_params; function_body; _ } ->
      Translate_context.term_references
        (List.map function_params ~f:(fun (id, _) -> id.S.pid_str))
        function_body
  | Proof_lemma
      {
        lemma_params;
        lemma_returns;
        lemma_requires;
        lemma_ensures;
        lemma_variant;
        lemma_body;
        _;
      } ->
      let bound =
        List.map (lemma_params @ lemma_returns) ~f:(fun (id, _) -> id.S.pid_str)
      in
      List.concat_map
        (lemma_requires @ lemma_ensures @ lemma_variant)
        ~f:(Translate_context.term_references bound)
      @ proof_references bound lemma_body
  | Proof_invariant { inv_params; inv_state = state, _; inv_body; _ } ->
      Translate_context.term_references
        (state.pid_str :: List.map inv_params ~f:(fun (id, _) -> id.S.pid_str))
        inv_body
  | Proof_view { view_params; view_value; _ } ->
      Translate_context.term_references
        (List.map view_params ~f:(fun (id, _) -> id.S.pid_str))
        view_value
  | Proof_action { action_update; action_consumes; action_helps; _ } ->
      let terms = List.map action_update ~f:snd @ Option.to_list action_consumes in
      let terms =
        terms
        @ Option.value_map action_helps ~default:[] ~f:(fun (a, b, c) -> [ a; b; c ])
      in
      List.concat_map terms ~f:(Translate_context.term_references [])
  | Proof_module _ | Proof_definition _ | Proof_type _ | Proof_resource _ | Proof_au _
  | Proof_field _ | Proof_state _ ->
      []

let annotation_references (annotation : Annotation.t) =
  let terms terms = List.concat_map terms ~f:(Translate_context.term_references []) in
  match Annotation.kind annotation with
  | Scope ->
      Result.map (Annotation.scope annotation) ~f:(fun scope ->
          proof_references [] scope.S.scope_body)
  | Returns ->
      Result.map (Annotation.returns annotation) ~f:(fun adapter ->
          proof_references [] adapter.S.returns_body)
  | Proof -> Result.map (Annotation.proof annotation) ~f:(proof_references [])
  | Ghost ->
      Result.map (Annotation.ghost_stmts annotation) ~f:(fun statements ->
          List.concat_map statements ~f:(function
            | S.Fold term
            | Unfold term
            | Assert term
            | Unfold_with (term, _)
            | Ghost_call term ->
                terms [ term ]
            | Fold_with (term, witnesses) -> terms (term :: List.map witnesses ~f:snd)))
  | Initializes ->
      Result.map (Annotation.initializes annotation) ~f:(fun term -> terms [ term ])
  | Initially | Contract | Loop | Predicate | Ghost_module | Manual | Linearization
  | Trusted ->
      Ok []

(** Nested functions are registered and scanned as their own declaration workers. *)
let rec runtime_references (expression : Typedtree.expression) =
  let children, paths =
    match expression.exp_desc with
    | Texp_ident (path, _, _) -> ([], [ path ])
    | Texp_let (_, bindings, body) ->
        (body :: List.map bindings ~f:(fun binding -> binding.Typedtree.vb_expr), [])
    | Texp_apply (callee, arguments) ->
        ( callee
          :: List.filter_map arguments ~f:(function
            | _, Typedtree.Arg argument -> Some argument
            | _, Omitted () -> None),
          [] )
    | Texp_match (value, cases, effects, _) ->
        ( (value :: List.map cases ~f:(fun case -> case.Typedtree.c_rhs))
          @ List.map effects ~f:(fun case -> case.Typedtree.c_rhs),
          [] )
    | Texp_try (value, cases, effects) ->
        (value :: List.map (cases @ effects) ~f:(fun case -> case.Typedtree.c_rhs), [])
    | Texp_tuple elements -> (List.map elements ~f:snd, [])
    | Texp_construct (_, _, arguments) | Texp_array (_, arguments) -> (arguments, [])
    | Texp_variant (_, value) -> (Option.to_list value, [])
    | Texp_record { fields; extended_expression; _ } ->
        ( Option.to_list extended_expression
          @ List.filter_map (Array.to_list fields) ~f:(function
            | _, Typedtree.Kept _ -> None
            | _, Overridden (_, value) -> Some value),
          [] )
    | Texp_atomic_loc (value, _, _)
    | Texp_field (value, _, _)
    | Texp_assert (value, _)
    | Texp_lazy value ->
        ([ value ], [])
    | Texp_setfield (value, _, _, content)
    | Texp_sequence (value, content)
    | Texp_while (value, content) ->
        ([ value; content ], [])
    | Texp_ifthenelse (condition, yes, no) -> (condition :: yes :: Option.to_list no, [])
    | Texp_for (_, _, first, last, _, body) -> ([ first; last; body ], [])
    | Texp_struct_item (_, rest) -> ([ rest ], [])
    | Texp_function _ | Texp_constant _ | Texp_send _ | Texp_new _ | Texp_instvar _
    | Texp_setinstvar _ | Texp_override _ | Texp_object _ | Texp_pack _ | Texp_letop _
    | Texp_unreachable | Texp_extension_constructor _ ->
        ([], [])
  in
  List.fold children ~init:([ expression.exp_type ], paths)
    ~f:(fun (types, paths) child ->
      let child_types, child_paths = runtime_references child in
      (child_types @ types, child_paths @ paths))

let create (scopes : Program_scopes.t) (decls : Program_declarations.t)
    (proofs : Program_proofs.t) =
  let source = decls.source in
  let assets =
    List.map decls.generic_resource_workers ~f:fst
    @ List.map decls.generic_model_workers ~f:fst
    @ List.filter_map source.proof_fields ~f:(fun field ->
        Option.some_if
          (not (List.is_empty field.Source.field_parameters))
          (Generic_fields.worker field))
  in
  let proof_workers = decls.generic_predicate_workers @ proofs.generic_callables in
  let workers = proof_workers @ assets in
  let runtime_path path =
    let direct =
      List.find_map decls.polymorphic_functions ~f:(fun worker ->
          Option.some_if
            (List.exists worker.Polymorphic_functions.paths ~f:(Path.same path)
            || Path.same path (Path.Pident worker.id))
            worker.name)
    in
    Option.first_some direct
      (List.find_map scopes.funcs ~f:(fun func ->
           if not (List.exists func.Procedures.paths ~f:(Path.same path)) then None
           else
             Option.bind (Generic_modules.member scopes.generics func.id)
               ~f:(fun (group, _, stem) ->
                 let source =
                   List.find_map group.body_members ~f:(fun (source, target) ->
                       Option.some_if (String.equal stem target) source)
                 in
                 let representative =
                   Option.bind source ~f:(fun source ->
                       List.Assoc.find group.representative.body_members source
                         ~equal:String.equal)
                 in
                 Option.bind representative ~f:(fun id ->
                     List.find_map decls.polymorphic_functions ~f:(fun worker ->
                         Option.some_if
                           (Ident.same worker.Polymorphic_functions.id id)
                           worker.name)))))
  in
  let worker_key key =
    List.find_map workers ~f:(fun worker ->
        Option.some_if (String.equal worker.Generic_parameters.key key) worker.name)
  in
  let au_worker au = runtime_path au.Source.au_operation_path in
  let resource_worker resource = worker_key resource.Source.resource_backend in
  let model_worker data =
    Option.map data.Datatypes.family ~f:(fun family -> family.Datatypes.worker)
  in
  let rec type_dependencies seen typ =
    let id = Types.get_id typ in
    if Set.mem seen id then []
    else
      let seen = Set.add seen id in
      let nested =
        Btype.fold_type_expr (fun found typ -> type_dependencies seen typ @ found) [] typ
      in
      match Types.get_desc typ with
      | Tconstr (path, _, _) ->
          let atomic =
            List.filter_map source.proof_aus ~f:(fun au ->
                if
                  Path.same path au.Source.au_token_path
                  || List.exists au.au_token_paths ~f:(Path.same path)
                then au_worker au
                else None)
          in
          let resources =
            List.filter_map decls.all_resources ~f:(fun resource ->
                if
                  List.exists
                    (resource.Source.resource_descriptor :: resource.resource_aliases)
                    ~f:(fun data -> Datatypes.declares data path)
                then resource_worker resource
                else None)
          in
          let models =
            Option.to_list (Option.bind (Datatypes.find decls.types path) ~f:model_worker)
          in
          atomic @ resources @ models @ nested
      | _ -> nested
  in
  let types_dependencies types =
    List.concat_map types ~f:(type_dependencies (Set.empty (module Int)))
  in
  let field_path path =
    List.find_map source.proof_fields ~f:(fun field ->
        if
          Path.same path field.Source.field_path
          || Path.same path (Path.Pident field.field_id)
        then Some field
        else None)
  in
  let reference ~environment ~scope q =
    let value = Option.to_list (Source.value_path environment q) in
    let runtime = List.filter_map value ~f:runtime_path in
    let fields =
      List.concat_map value ~f:(fun path ->
          Option.value_map (field_path path) ~default:[] ~f:(fun field ->
              match worker_key field.field_backend with
              | Some name -> [ name ]
              | None -> types_dependencies [ field.field_owner; field.field_value ]))
    in
    let proof =
      Option.to_list
        (match Proof_bindings.resolve scopes.scoped_proofs ~scope ~environment q with
        | Some key -> worker_key key
        | None -> (
            match q with
            | S.Qid id ->
                let namespace =
                  Option.value_map scope ~default:[] ~f:(fun scope ->
                      scope.Proof_scopes.namespace)
                in
                let rec lexical namespace =
                  let candidate = String.concat ~sep:"." (namespace @ [ id.pid_str ]) in
                  match worker_key candidate with
                  | Some _ as found -> found
                  | None -> Option.bind (List.drop_last namespace) ~f:lexical
                in
                lexical namespace
            | Qdot _ -> None))
    in
    let modules =
      match q with
      | S.Qid _ -> []
      | Qdot (parent, _) -> Option.to_list (Source.module_path environment parent)
    in
    let atomic =
      List.concat_map modules ~f:(fun path ->
          List.filter_map source.proof_aus ~f:(fun au ->
              if Source.au_has_path au path then au_worker au else None))
    in
    let resources =
      List.concat_map modules ~f:(fun path ->
          List.filter_map decls.all_resources ~f:(fun resource ->
              if Source.resource_has_path resource path then resource_worker resource
              else None))
    in
    runtime @ fields @ proof @ atomic @ resources
  in
  let references ~environment ~scope refs =
    List.concat_map refs ~f:(reference ~environment ~scope)
  in
  let binding key =
    List.find scopes.scoped_proofs.bindings ~f:(fun binding ->
        String.equal binding.Proof_bindings.backend key
        || String.equal binding.public_key key)
  in
  let worker_node ?context (worker : Generic_parameters.t) =
    let context =
      Option.value_or_thunk context ~default:(fun () ->
          Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
            ~unapplied_proofs:scopes.unapplied_proofs worker.key)
    in
    let dependencies = types_dependencies worker.parameters in
    let dependencies =
      match binding worker.key with
      | None ->
          let entry =
            List.find source.proof_scopes.declarations ~f:(fun entry ->
                String.equal worker.key
                  (String.concat ~sep:"."
                     (entry.Proof_scopes.scope.namespace @ [ entry.name.pid_str ])))
          in
          Option.value_map entry ~default:dependencies ~f:(fun entry ->
              references
                ~environment:(Source.annotation_env source entry.scope.environment)
                ~scope:(Some entry.scope)
                (declaration_references entry.declaration)
              @ dependencies)
      | Some binding ->
          references ~environment:binding.environment ~scope:(Some binding.entry.scope)
            (declaration_references binding.entry.declaration)
          @ types_dependencies binding.private_types
          @ dependencies
    in
    Generic_families.
      {
        name = worker.name;
        scope = context.namespace;
        variables = worker.variables;
        at = worker.loc;
        dependencies;
      }
  in
  let runtime_nodes =
    List.map decls.polymorphic_functions ~f:(fun worker ->
        let func =
          List.find scopes.funcs ~f:(fun func ->
              Ident.same func.Procedures.id worker.Polymorphic_functions.id)
        in
        let dependencies = types_dependencies [ worker.scheme.typ ] in
        let dependencies =
          Option.value_map func ~default:dependencies ~f:(fun func ->
              let scope =
                Proof_scopes.find_namespace source.proof_scopes func.namespace
              in
              let terms = Option.value_map func.contract ~default:[] ~f:contract_terms in
              let refs =
                List.concat_map terms
                  ~f:
                    (Translate_context.term_references
                       (Procedures.contract_bound_names func))
              in
              let refs =
                refs
                @ List.concat_map scopes.annotations ~f:(fun annotation ->
                    if
                      annotation.Annotation.loc.loc_start.pos_cnum
                      >= func.loc.loc_start.pos_cnum
                      && annotation.loc.loc_end.pos_cnum <= func.loc.loc_end.pos_cnum
                    then
                      Option.value
                        (Result.ok (annotation_references annotation))
                        ~default:[]
                    else [])
              in
              let types, paths = runtime_references func.body in
              types_dependencies types
              @ List.filter_map paths ~f:runtime_path
              @ references ~environment:func.environment ~scope refs
              @ dependencies)
        in
        Generic_families.
          {
            name = worker.name;
            scope = (Qualified_name.of_string worker.name).path;
            variables = worker.scheme.variables;
            at = worker.loc;
            dependencies;
          })
  in
  let model_nodes =
    List.map decls.generic_model_workers ~f:(fun (worker, _) ->
        let data =
          List.find decls.types ~f:(fun data ->
              Option.exists (model_worker data) ~f:(String.equal worker.name))
        in
        let context =
          Option.map data ~f:(fun data ->
              Module_context.for_scope scopes.module_contexts
                (Generic_proofs.model_owner source data))
        in
        let node = worker_node ?context worker in
        let dependencies =
          Option.value_map data ~default:node.dependencies ~f:(fun data ->
              List.concat_map data.ctors ~f:(fun ctor ->
                  types_dependencies ctor.Datatypes.args)
              @ node.dependencies)
        in
        { node with dependencies })
  in
  let resource_nodes =
    List.map decls.generic_resource_workers ~f:(fun (worker, _) ->
        let resource =
          List.find decls.all_resources ~f:(fun resource ->
              String.equal resource.Source.resource_backend worker.key)
        in
        let context =
          Option.map resource ~f:(fun resource ->
              Program_scopes.asset_context ~module_contexts:scopes.module_contexts
                resource.Source.resource_scope)
        in
        let node = worker_node ?context worker in
        let dependencies =
          Option.value_map resource ~default:node.dependencies ~f:(fun resource ->
              types_dependencies
                (Generic_assets.argument_types decls.all_resources resource)
              @ node.dependencies)
        in
        { node with dependencies })
  in
  let fields =
    List.filter source.proof_fields ~f:(fun field ->
        not (List.is_empty field.Source.field_parameters))
  in
  let nodes =
    runtime_nodes
    @ List.map proof_workers ~f:(fun worker -> worker_node worker)
    @ List.map fields ~f:(fun field ->
        let context =
          Program_scopes.asset_context ~module_contexts:scopes.module_contexts
            field.Source.field_scope
        in
        worker_node ~context (Generic_fields.worker field))
    @ resource_nodes @ model_nodes
  in
  Result.map (Generic_families.create nodes) ~f:(fun families -> { families })
