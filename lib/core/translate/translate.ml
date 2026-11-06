(** The translation of OCaml implementations to Raven programs.

    So far: top-level functions on integers, booleans, unit, tuples and variant types,
    with their contracts. A function becomes a procedure, and a variant type a data type
    (see {!Datatypes}). Expressions are put in A-normal form, since a call is a statement
    in Raven; arguments are evaluated right to left, as OCaml does. *)

open Base
open Translate_context
open Procedures
open Program_items

type callable_worker =
  | Runtime_worker of Polymorphic_functions.t
  | Proof_worker of Generic_parameters.t

let callable_name = function
  | Runtime_worker worker -> worker.Polymorphic_functions.name
  | Proof_worker worker -> worker.Generic_parameters.name

let callable_location = function
  | Runtime_worker worker -> worker.Polymorphic_functions.loc
  | Proof_worker worker -> worker.Generic_parameters.loc

(** The Raven program translating [source], with its histories encoded in [history], and
    the origins of its proof obligations. *)
let program_with_diagnostics ?(history = History.default) ?scopes (source : Source.t) :
    (R.Program.t * origin list * R.Diagnostic.t list, error) Result.t =
  let* scopes =
    match scopes with Some scopes -> Ok scopes | None -> Program_scopes.run source
  in
  let* scopes = Program_declarations.specialize_continuations scopes in
  let {
    Program_scopes.annotations;
    linearizations;
    initializations;
    source;
    implementation;
    proof_implementation;
    definition_target;
    inventory;
    definition_member_name;
    libraries;
    funcs;
    specialized = _;
    access_proofs;
    return_proofs;
    types;
    public_types;
    generics;
    generic_proofs;
    module_contexts;
    generic_proof_types;
    scoped_proofs;
    unapplied_proofs;
  } =
    scopes
  in
  let definition_resource = Program_scopes.definition_resource ~source:scopes.source in
  let scoped_binding =
    Program_scopes.scoped_binding ~unapplied_proofs:scopes.unapplied_proofs
  in
  let snapshot = Fresh_names.save () in
  let declare family_plan =
    let* decls = Program_declarations.run ~family_plan scopes in
    let* proofs, state = Program_proofs.run ~family_plan scopes decls State.initial in
    Ok (decls, proofs, state)
  in
  let complete (decls, proofs, state) =
    let* shaped = Program_structures.run ~history scopes decls proofs in
    let* translated, state = Program_members.run scopes decls proofs shaped state in
    Ok (decls, proofs, shaped, translated, state)
  in
  (* Every worker's functor, as [rename] assigns it, and the workers. *)
  let family_plan ~rename (decls : Program_declarations.t) (proofs : Program_proofs.t) =
    let assets =
      List.map (decls.generic_resource_workers @ decls.generic_model_workers) ~f:fst
      @ List.filter_map decls.source.proof_fields ~f:(fun field ->
          Option.some_if
            (not (List.is_empty field.Source.field_parameters))
            (Generic_fields.worker field))
    in
    let proofs = decls.generic_predicates @ proofs.generic_callables in
    let workers =
      List.map decls.polymorphic_functions ~f:(fun worker ->
          {
            Worker_groups.name = worker.Polymorphic_functions.name;
            arity = List.length worker.scheme.variables;
            witness = Option.is_some worker.witness;
          })
      @ List.map (proofs @ assets) ~f:(fun worker ->
          {
            Worker_groups.name = worker.Generic_parameters.name;
            arity = List.length worker.variables;
            witness = false;
          })
    in
    ( Generic_family_plan.
        {
          runtime =
            List.map decls.polymorphic_functions ~f:(fun worker ->
                (worker.Polymorphic_functions.id, rename worker.name));
          proofs =
            List.map proofs ~f:(fun worker ->
                (worker.Generic_parameters.key, rename worker.name));
          assets =
            List.map assets ~f:(fun worker ->
                (worker.Generic_parameters.key, rename worker.name));
        },
      List.dedup_and_sort workers ~compare:(fun left right ->
          String.compare left.Worker_groups.name right.name) )
  in
  let* decls, proofs, shaped, translated, state =
    let* ((decls, proofs, _) as declared) = declare Generic_family_plan.empty in
    let* dependencies = Generic_dependencies.create scopes decls proofs in
    let* declared =
      if
        List.exists dependencies.families.groups ~f:(fun group ->
            List.length group.Generic_families.members > 1)
      then
        declare
          (fst
             (family_plan
                ~rename:(Generic_families.normalize_name dependencies.families)
                decls proofs))
      else Ok declared
    in
    let* ((decls, proofs, _, _, state) as completed) = complete declared in
    let _, workers = family_plan ~rename:Fn.id decls proofs in
    let rec generic_modules (group : Generic_modules.t) =
      group :: List.concat_map group.captures ~f:generic_modules
    in
    let generic_modules = List.concat_map scopes.generics ~f:generic_modules in
    let applications =
      List.concat_map generic_modules ~f:(fun group ->
          List.map group.applications ~f:(fun application -> (group, application)))
    in
    (* Root functions follow the module applications before them. *)
    let lexical =
      List.concat_map decls.polymorphic_functions ~f:(fun worker ->
          if not (List.is_empty (Qualified_name.of_string worker.name).path) then []
          else
            List.filter_map applications ~f:(fun (_, application) ->
                Option.some_if
                  (application.source.argument.site.item_loc.loc_start.pos_cnum
                 < worker.loc.loc_start.pos_cnum)
                  {
                    Worker_groups.namespace = [ worker.name ];
                    target = application.name ^ ".";
                    arguments = None;
                  }))
    in
    let* groups =
      Worker_groups.create
        ~generic_modules:(List.map generic_modules ~f:(fun group -> group.name))
        ~applications:
          (List.map applications ~f:(fun (group, application) ->
               (application.name, group.name)))
        workers
        (List.map state.tables.function_instances ~f:(fun instance ->
             {
               Worker_groups.namespace = instance.instance_namespace;
               target = instance.instance_worker;
               arguments = Some instance.instance_arguments;
             })
        @ List.map state.tables.call_targets ~f:(fun (namespace, target) ->
            { Worker_groups.namespace; target; arguments = None })
        @ lexical)
    in
    if List.is_empty groups then Ok completed
    else begin
      (* Translated again, naming everything as before. *)
      Fresh_names.restore snapshot;
      Fresh_names.reserve (List.map workers ~f:(fun worker -> worker.Worker_groups.name));
      let functors =
        List.concat_map groups ~f:(fun members ->
            let scope = (Qualified_name.of_string (List.hd_exn members)).path in
            let name = String.concat ~sep:"." (scope @ [ Fresh_names.fresh "Generic" ]) in
            List.map members ~f:(fun member -> (member, name)))
        |> Map.of_alist_exn (module String)
      in
      let plan, _ =
        family_plan
          ~rename:(fun name -> Option.value (Map.find functors name) ~default:name)
          decls proofs
      in
      let* declared = declare plan in
      complete declared
    end
  in
  let {
    Program_declarations.source;
    all_resources;
    all_resource_views;
    private_ra_types;
    proof_assets;
    layouts;
    checked_modules;
    checked_operations;
    pure;
    runtime_destinations;
    procedure_signatures;
    atomic_operations;
    token_types;
    generic_models;
    resource_types;
    types;
    native_resource_members;
    generic_resource_workers;
    generic_model_workers;
    imported_resource_members;
    public_resource_members;
    deferred_native_resource_members;
    pending_declarations;
    pending_fields;
    modules;
    fields;
    functions;
    lifted;
    ocaml_env;
    scoped_proofs;
    scoped_inputs;
    predicates;
    library_preds;
    procedures;
    generic_procedures;
    polymorphic_functions;
    generic_predicates;
    generic_predicate_workers;
  } =
    decls
  in
  let body_destination =
    Program_declarations.body_destination ~polymorphic_functions ~generics:scopes.generics
      ~module_contexts:scopes.module_contexts
      ~context_for_group:
        (Program_scopes.context_for_group ~module_contexts:scopes.module_contexts)
  in
  let {
    Program_proofs.checked_views;
    checked_resource_entries;
    logical_declarations;
    all_logical_functions;
    generic_callables;
    proof_support;
    preds;
    spec_funcs;
    lemma_declarations;
    lemma_context;
    module_parameters;
    private_scoped_inputs;
    proof_env;
  } =
    proofs
  in
  let {
    Program_structures.structures;
    structure_member_lists;
    view_fields;
    past_structures;
    pasts;
    past_returns;
    ghost_args;
    _;
  } =
    shaped
  in
  let owner_destination =
    Program_structures.owner_destination
      ~declaration_context:
        (Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
           ~unapplied_proofs:scopes.unapplied_proofs)
  in
  let predicate_destination =
    Program_declarations.predicate_destination ~generic_predicates
      ~declaration_context:
        (Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
           ~unapplied_proofs:scopes.unapplied_proofs)
  in
  let field_group = Program_structures.field_group ~generics:scopes.generics in
  let state_members =
    Program_structures.state_members ~destination_of:predicate_destination
  in
  let {
    Program_members.library_modules = library_parts;
    library_worker_members;
    publication_members;
    generic_interfaces;
    checked_module_members;
    type_constructor_factories;
    action_check_lists;
    pending_member_lists;
    pred_members;
    lemma_members;
    logical_members;
    pure_funcs;
    procs;
  } =
    translated
  in
  let owned destination members =
    List.filter members ~f:(fun (f, _) ->
        Module_context.same_destination destination (body_destination f))
  in
  let procedure_member (f, member) =
    if f.trusted then R.Member.free (R.Member.callable member)
    else R.Member.callable member
  in
  let predicate_members =
    List.zip_exn
      (List.map predicates ~f:(fun (_, p, _, _) -> p.S.pred_name.pid_str))
      pred_members
  in
  let emitted_predicates destination =
    List.concat_map predicate_members ~f:(fun (key, (member, parts)) ->
        if Module_context.same_destination destination (predicate_destination key) then
          member :: parts
        else [])
  in
  let proof_member key member =
    if
      Option.exists (scoped_binding key) ~f:(fun binding ->
          Source.trusted_proof source binding.entry.scope.owner)
    then R.Member.free member
    else member
  in
  let proof_lemma_members =
    List.map2_exn lemma_declarations lemma_members ~f:(fun declaration member ->
        let name = Proof_scopes.name declaration in
        let member = R.Member.callable member in
        (name.pid_str, proof_member name.pid_str member))
  in
  let logical_members =
    List.map2_exn logical_declarations logical_members ~f:(fun declaration member ->
        let name = Proof_scopes.name declaration in
        (name.pid_str, proof_member name.pid_str member))
  in
  let proof_members =
    List.concat_map predicate_members ~f:(fun (name, (member, parts)) ->
        List.map (member :: parts) ~f:(fun member -> (name, R.Member.callable member)))
    @ proof_lemma_members @ logical_members
  in
  (* A proof member's callables: a predicate's come with its parts'. *)
  let members_named backend =
    List.filter_map proof_members ~f:(fun (name, member) ->
        Option.some_if (String.equal name backend) member)
  in
  let* definition_modules =
    all
      (List.filter source.proof_resources ~f:(fun resource ->
           resource.Source.resource_definition
           && Option.is_none resource.resource_application))
      ~f:(fun resource ->
        let at = resource.resource_at in
        let l = loc at in
        let* backend, representation =
          match (implementation resource, resource.resource_representation) with
          | Some backend, Some representation -> Ok (backend, representation)
          | _ -> error at "Missing resource algebra representation"
        in
        let* representation = Datatypes.typ types ~at representation in
        let carrier =
          R.Member.type_ ~loc:l ~rep:true (ident ~loc:l "T") (Some representation)
        in
        let members =
          List.concat_map source.proof_scopes.declarations ~f:(fun entry ->
              Option.value_map ~default:[]
                (List.find scoped_proofs.bindings ~f:(fun binding ->
                     Ident.same binding.entry.id entry.id
                     && (match binding.kind with Function _ -> true | _ -> false)
                     && Option.exists (definition_resource binding.entry.scope)
                          ~f:(fun owner ->
                            Ident.same owner.resource_id resource.resource_id)))
                ~f:(fun binding -> members_named binding.backend))
        in
        let interface =
          qualified_name ~loc:l (String.concat ~sep:"." resource.resource_functor)
        in
        Ok
          ( resource,
            R.Member.module_ ~loc:l
              ~implements:[ (interface, []) ]
              (ident ~loc:l backend) (carrier :: members) ))
  in
  let definition_proof_modules =
    List.filter_map source.proof_resources ~f:(fun resource ->
        if
          (not resource.resource_definition)
          || Option.is_some resource.resource_application
        then None
        else
          Option.bind (proof_implementation resource) ~f:(fun backend ->
              let members =
                List.concat_map source.proof_scopes.declarations ~f:(fun entry ->
                    Option.value_map ~default:[]
                      (List.find scoped_proofs.bindings ~f:(fun binding ->
                           Ident.same binding.entry.id entry.id
                           && (match binding.kind with
                             | Predicate _ | Lemma _ -> true
                             | _ -> false)
                           && Option.exists (definition_resource binding.entry.scope)
                                ~f:(fun owner ->
                                  Ident.same owner.resource_id resource.resource_id)))
                      ~f:(fun binding -> members_named binding.backend))
              in
              Option.some_if
                (not (List.is_empty members))
                ( resource,
                  R.Member.module_ ~loc:(loc resource.resource_at)
                    (ident ~loc:(loc resource.resource_at) backend)
                    members )))
  in
  let proof_destination name =
    let parent = owner_destination name in
    match Generic_parameters.find generic_callables name with
    | None -> parent
    | Some worker -> Module_context.Proof_worker (worker, parent)
  in
  let emitted_proofs destination members =
    List.filter_map members ~f:(fun (name, member) ->
        Option.some_if
          (Module_context.same_destination (proof_destination name) destination
          && Option.is_none (Option.bind (scoped_binding name) ~f:definition_target))
          member)
  in
  let emitted_assets destination members =
    List.filter_map members ~f:(fun (resource, member) ->
        Option.some_if
          (Module_context.emits_owner module_contexts ~destination
             resource.Source.resource_scope)
          member)
  in
  let* (), state =
    State.run_from state
      (State.map
         (State.all source.proof_resources ~f:(fun resource ->
              match Generic_assets.resource_worker resource with
              | None -> State.return ()
              | Some worker ->
                  let local_resources =
                    List.filter all_resources ~f:(fun candidate ->
                        Option.is_none candidate.Source.resource_application
                        && Option.equal Path.same candidate.resource_scope
                             resource.resource_scope)
                  in
                  let resources = local_resources @ all_resources in
                  let data =
                    Generic_parameters.types worker
                      (Generic_assets.types local_resources types)
                  in
                  State.map
                    (State.all
                       (Generic_assets.argument_types resources resource)
                       ~f:(State.note_domain data))
                    ~f:(fun _ -> ())))
         ~f:(fun _ -> ()))
  in
  let model_families =
    List.filter types ~f:(fun data ->
        (not (List.is_empty data.Datatypes.ctors))
        && Option.exists data.family ~f:(fun family ->
            List.exists generic_model_workers ~f:(fun (worker, _) ->
                String.equal family.Datatypes.worker worker.Generic_parameters.name)))
    |> List.fold
         ~init:(Set.empty (module String), [])
         ~f:(fun (seen, models) data ->
           let key = Generic_models.name data in
           if Set.mem seen key then (seen, models) else (Set.add seen key, data :: models))
    |> snd |> List.rev
  in
  let* (), state =
    State.run_from state
      (State.map
         (State.all model_families ~f:(fun data ->
              match data.Datatypes.family with
              | Some _ when not (List.is_empty data.ctors) ->
                  let worker = Generic_models.worker data in
                  let types = Generic_parameters.types worker types in
                  State.map
                    (State.all
                       (List.concat_map data.ctors ~f:(fun ctor -> ctor.Datatypes.args))
                       ~f:(State.note_domain types))
                    ~f:(fun _ -> ())
              | _ -> State.return ()))
         ~f:(fun _ -> ()))
  in
  let generic_fields =
    List.filter_map source.proof_fields ~f:(fun field ->
        Option.some_if
          (not (List.is_empty field.Source.field_parameters))
          (Generic_fields.worker field))
  in
  let emitted_fields destination fields =
    List.filter_map fields ~f:(fun (field, member) ->
        Option.some_if
          (if List.is_empty field.Source.field_parameters then
             Module_context.emits_owner module_contexts ~destination field.field_scope
           else
             List.equal String.equal
               (Module_context.namespace destination)
               (String.split (Generic_fields.worker field).name ~on:'.'))
          member)
  in
  let raw_resource_field field =
    Option.is_some field.Source.field_resource
    || List.exists all_resource_views ~f:(fun resource ->
        resource.Source.resource_is_ra
        && same_named_type field.field_value resource.resource_type)
  in
  let resource_field_type types resources (field : Source.proof_field) resource =
    let resource =
      Generic_assets.local_resource ~scope:field.field_scope resources resource
    in
    let arguments =
      match Datatypes.desc types field.field_value with
      | Tconstr (_, arguments, _) -> arguments
      | _ -> []
    in
    match Generic_assets.native_module types resource arguments with
    | Some backend ->
        let l = loc field.field_at in
        Ok (R.Type.named ~loc:l (qualified_name ~loc:l backend) [])
    | None -> error field.field_at "This resource field type instance cannot be inferred"
  in
  let* explicit_fields, state =
    State.run_from state
      (State.all source.proof_fields ~f:(fun field ->
           let local_resources =
             List.filter all_resource_views ~f:(fun resource ->
                 Option.is_none resource.Source.resource_application
                 && Option.equal Path.same resource.resource_scope
                      field.Source.field_scope)
           in
           let resources = local_resources @ all_resource_views in
           let types = Generic_assets.types local_resources types in
           let types =
             if List.is_empty field.Source.field_parameters then types
             else Generic_parameters.types (Generic_fields.worker field) types
           in
           let open State.Syntax in
           let* () = State.note_domain types field.field_value in
           let l = loc field.Source.field_at in
           let computation =
             let ( let* ) = Result.( >>= ) in
             let* value_type =
               match field.field_resource with
               | None ->
                   begin match
                     List.find resources ~f:(fun resource ->
                         resource.resource_is_ra
                         && same_named_type field.field_value resource.resource_type)
                   with
                   | None -> Datatypes.typ types ~at:field.field_at field.field_value
                   | Some resource when not (List.is_empty resource.resource_parameters)
                     ->
                       resource_field_type types resources field resource
                   | Some resource ->
                       Ok
                         (R.Type.named ~loc:l
                            (qualified_name ~loc:l resource.resource_backend)
                            [])
                   end
               | Some owner ->
                   begin match Generic_assets.find_resource resources owner with
                   | None -> error field.field_at "Unknown resource algebra for field"
                   | Some resource when not (List.is_empty resource.resource_parameters)
                     ->
                       resource_field_type types resources field resource
                   | Some resource ->
                       let private_representation =
                         resource.resource_definition
                         && Option.exists resource.resource_representation ~f:(fun rep ->
                             same_named_type field.field_value rep)
                       in
                       let* backend =
                         if private_representation then
                           match implementation resource with
                           | Some backend -> Ok backend
                           | None ->
                               error field.field_at
                                 "Missing resource algebra implementation"
                         else Ok resource.resource_backend
                       in
                       if resource.resource_is_ra then
                         Ok (R.Type.named ~loc:l (qualified_name ~loc:l backend) [])
                       else
                         error field.field_at
                           "The field resource is not a resource algebra"
                   end
             in
             Ok
               ( field,
                 let field_name =
                   (Qualified_name.of_string (ghost_field_name field)).name
                 in
                 if raw_resource_field field then
                   R.Member.field ~ghost:true ~loc:l (ident ~loc:l field_name) value_type
                 else
                   Datatypes.field_member ~ghost:true types ~loc:l field_name value_type
                     field.field_value )
           in
           State.of_result computation))
  in
  let field_domain_types =
    List.concat_map types ~f:(fun data ->
        List.map (Option.value data.Datatypes.heap ~default:[]) ~f:(fun field ->
            field.Datatypes.typ))
  in
  let* argument_domains =
    all generics ~f:(fun group ->
        all group.Generic_modules.applications ~f:(fun application ->
            all application.source.parameters ~f:(fun parameter ->
                let concrete =
                  checked_raw_types types parameter.Module_inventory.argument
                in
                Ok
                  (List.filter_map parameter.argument.expected.signature_types
                     ~f:(fun (_, declaration) ->
                       Option.some_if
                         (Option.is_none declaration.Typedtree.typ_manifest
                         && Generic_type_families.arity declaration = 0)
                         {
                           domain_types = concrete;
                           domain_type =
                             Ctype.newconstr (Path.Pident declaration.typ_id) [];
                         }))))
        |> Result.map ~f:(fun groups -> List.concat (List.concat groups)))
    |> Result.map ~f:List.concat
  in
  let argument_domains = argument_domains @ state.tables.dictionaries in
  let layout_domain_requests =
    List.concat_map types ~f:(fun data ->
        if
          data.Datatypes.mathematical
          || (not (List.is_empty data.parameters))
          || not (Result_layouts.contains layouts data)
        then []
        else
          List.concat_map data.ctors ~f:(fun ctor ->
              List.map ctor.Datatypes.args ~f:(fun t ->
                  { domain_types = types; domain_type = t })))
  in
  let registered_domains = state.tables.domains @ layout_domain_requests in
  let domain_requests = registered_domains @ argument_domains in
  let domain_dependencies request =
    Result_layouts.type_dependencies
      ~additional:(Generic_proofs.layout_dependencies generic_proofs)
      layouts request.domain_types request.domain_type
  in
  let _, family_types =
    List.fold types
      ~init:(Set.empty (module String), [])
      ~f:(fun (seen, families) data ->
        let name = Datatypes.value_family_name data in
        let generic_model =
          List.exists generic_proofs ~f:(fun plan ->
              List.exists (Generic_proofs.models source plan) ~f:(fun model ->
                  Poly.equal model.Datatypes.at data.Datatypes.at))
        in
        if
          generic_model
          || (not (Datatypes.is_value_family data))
          || Option.value_map data.module_path ~default:false ~f:(fun path ->
              List.length path <> 1)
          || Set.mem seen name
        then (seen, families)
        else (Set.add seen name, data :: families))
  in
  let* value_family_parts =
    all (List.rev family_types) ~f:(Datatypes.value_family_members types)
  in
  let* witness_parts =
    all
      (List.filter types ~f:(fun data -> Option.is_some data.Datatypes.witness))
      ~f:(Witnesses.members types)
  in
  let value_family_parts = value_family_parts @ witness_parts in
  let value_factory_templates = List.concat_map value_family_parts ~f:snd in
  let value_factory_names =
    List.concat_map value_family_parts ~f:(fun (members, _) -> List.map members ~f:fst)
    |> Set.of_list (module String)
  in
  let* domain_groups =
    let* registered =
      all registered_domains ~f:(fun request ->
          let* members =
            Datatypes.domain_members request.domain_types [ request.domain_type ]
          in
          Ok (domain_dependencies request, members))
    in
    let* arguments =
      all argument_domains ~f:(fun request ->
          let* members =
            Datatypes.domain_members ~dictionaries:true request.domain_types
              [ request.domain_type ]
          in
          Ok (domain_dependencies request, members))
    in
    let* fields =
      all field_domain_types ~f:(fun t ->
          let* members = Datatypes.domain_members types [ t ] in
          Ok
            ( Result_layouts.type_dependencies
                ~additional:(Generic_proofs.layout_dependencies generic_proofs)
                layouts types t,
              members ))
    in
    Ok (registered @ arguments @ fields)
  in
  (* Factory prerequisites retain their declaration order. *)
  let value_domains =
    Datatypes.unique_domain_members (List.concat_map domain_groups ~f:snd)
    |> List.filter ~f:(fun (name, _) -> not (Set.mem value_factory_names name))
  in
  let ordinary_value_templates =
    List.concat_map registered_domains ~f:(fun request ->
        Datatypes.value_templates request.domain_types [ request.domain_type ])
    @ List.concat_map argument_domains ~f:(fun request ->
        Datatypes.value_templates ~dictionaries:true request.domain_types
          [ request.domain_type ])
    @ Datatypes.value_templates types field_domain_types
  in
  let family_domain_names =
    List.concat_map domain_requests ~f:(fun request ->
        Datatypes.family_domain_dependencies ~dictionaries:true request.domain_types
          [ request.domain_type ]
        |> List.filter_map ~f:(fun (name, families) ->
            Option.some_if (not (List.is_empty families)) name))
    |> Set.of_list (module String)
  in
  let root_domain_declarations =
    List.filter_map value_domains ~f:(fun (name, member) ->
        Option.some_if
          (List.is_empty (Qualified_name.of_string name).path
          && not (Set.mem family_domain_names name))
          ( List.filter_map domain_groups ~f:(fun (dependencies, members) ->
                Option.some_if
                  (List.exists members ~f:(fun (candidate, _) ->
                       String.equal candidate name))
                  dependencies)
            |> List.reduce ~f:(fun left right ->
                List.filter left ~f:(fun dependency ->
                    List.mem right dependency ~equal:String.equal))
            |> Option.value ~default:[],
            [ member ] ))
  in
  let ready_domains, deferred_domains =
    Program_declarations.take_declarations ~available:[] root_domain_declarations
  in
  let deferred_native_binding binding =
    let captured =
      List.exists generics ~f:(fun group ->
          List.exists group.Generic_modules.captures ~f:(fun stage ->
              List.exists stage.applications ~f:(fun application ->
                  phys_equal application.source.argument binding)))
    in
    let final =
      List.exists generics ~f:(fun group ->
          List.exists group.Generic_modules.applications ~f:(fun application ->
              phys_equal application.source.argument binding))
    in
    captured && not final
  in
  let candidates =
    List.map
      (generic_predicate_workers @ generic_callables @ generic_fields
      @ List.map (generic_resource_workers @ generic_model_workers) ~f:fst)
      ~f:(fun worker -> Proof_worker worker)
    @ List.map polymorphic_functions ~f:(fun worker -> Runtime_worker worker)
    |> List.dedup_and_sort ~compare:(fun left right ->
        String.compare (callable_name left) (callable_name right))
  in
  let owns worker namespace =
    List.is_prefix namespace
      ~prefix:(String.split (callable_name worker) ~on:'.')
      ~equal:String.equal
  in
  let targets worker =
    List.filter_map state.tables.function_instances ~f:(fun instance ->
        Option.some_if (owns worker instance.instance_namespace) instance.instance_worker)
    @ List.filter_map state.tables.call_targets ~f:(fun (namespace, target) ->
        Option.some_if (owns worker namespace) target)
  in
  let calls target worker =
    List.is_prefix (String.split target ~on:'.')
      ~prefix:(String.split (callable_name worker) ~on:'.')
      ~equal:String.equal
  in
  let dependencies worker =
    let namespace = (Qualified_name.of_string (callable_name worker)).path in
    List.filter_map candidates ~f:(fun dependency ->
        Option.some_if
          ((not (String.equal (callable_name dependency) (callable_name worker)))
          && List.equal String.equal namespace
               (Qualified_name.of_string (callable_name dependency)).path
          && List.exists (targets worker) ~f:(fun target -> calls target dependency))
          (callable_name dependency))
  in
  let* callable_workers =
    Polymorphic_functions.order_by candidates ~name:callable_name
      ~location:callable_location ~dependencies
  in
  let root_callable_workers =
    List.filter callable_workers ~f:(fun worker ->
        List.is_empty (Qualified_name.of_string (callable_name worker)).path)
  in
  let function_value_types typ =
    let rec collect typ =
      match Datatypes.desc types typ with
      | Tarrow (_, argument, result, _) -> argument :: collect result
      | Tpoly (body, []) -> collect body
      | _ -> [ typ ]
    in
    collect typ
  in
  let lexical_dependencies position =
    List.concat_map generics ~f:(fun group ->
        List.filter_map group.Generic_modules.applications ~f:(fun application ->
            Option.some_if
              (application.source.argument.site.item_loc.loc_start.pos_cnum < position)
              application.name))
    @ List.filter_map checked_modules ~f:(fun view ->
        Option.some_if
          ((not (deferred_native_binding view.Checked_modules.binding))
          && view.binding.site.item_loc.loc_start.pos_cnum <= position)
          view.name)
  in
  let application_dependencies target =
    List.concat_map generics ~f:(fun group ->
        List.filter_map group.Generic_modules.applications ~f:(fun application ->
            Option.some_if
              (List.is_prefix (String.split target ~on:'.')
                 ~prefix:(String.split application.name ~on:'.')
                 ~equal:String.equal)
              application.name))
    @ List.filter_map checked_modules ~f:(fun view ->
        Option.some_if
          (List.is_prefix (String.split target ~on:'.')
             ~prefix:(String.split view.Checked_modules.name ~on:'.')
             ~equal:String.equal)
          view.name)
  in
  let worker_dependencies =
    List.fold root_callable_workers
      ~init:(Map.empty (module String))
      ~f:(fun previous worker ->
        let lexical =
          match worker with
          | Proof_worker _ -> []
          | Runtime_worker worker ->
              let position =
                List.fold inventory.specializations ~init:worker.loc.loc_start.pos_cnum
                  ~f:(fun position specialization ->
                    if
                      List.exists specialization.Module_inventory.body_members
                        ~f:(fun (_, id) -> Ident.same id worker.id)
                    then
                      Int.max position
                        specialization.argument.site.item_loc.loc_start.pos_cnum
                    else position)
              in
              lexical_dependencies position
        in
        let parameters =
          match worker with
          | Runtime_worker worker -> function_value_types worker.scheme.typ
          | Proof_worker worker ->
              worker.parameters
              @ List.concat_map generic_predicates ~f:(fun declaration ->
                  if String.equal declaration.Generic_parameters.name worker.name then
                    declaration.parameters
                  else [])
              @ List.concat_map structures ~f:(fun st ->
                  if
                    Option.exists st.generic ~f:(fun generic ->
                        String.equal generic.name worker.name)
                  then List.map st.fields ~f:(fun (_, _, _, typ, _) -> typ)
                  else [])
        in
        let layouts =
          List.concat_map parameters
            ~f:
              (Result_layouts.type_dependencies
                 ~additional:(Generic_proofs.layout_dependencies generic_proofs)
                 layouts types)
        in
        let called =
          List.concat_map (dependencies worker) ~f:(fun dependency ->
              Option.value (Map.find previous dependency) ~default:[])
        in
        let targets = targets worker in
        let applications = List.concat_map targets ~f:application_dependencies in
        let source_dependencies =
          List.concat_map targets ~f:(fun target ->
              List.concat_map pure ~f:(fun function_ ->
                  if
                    String.equal target
                      (Qualified_name.to_string
                         (Program_declarations.pure_reference ~generics function_))
                  then lexical_dependencies function_.loc.loc_start.pos_cnum
                  else []))
        in
        Map.set previous ~key:(callable_name worker)
          ~data:
            (List.dedup_and_sort
               (lexical @ layouts @ called @ applications @ source_dependencies)
               ~compare:String.compare))
  in
  let take_available ~available (declarations, domains, workers, fields) =
    let declarations, pending_declarations =
      Program_declarations.take_declarations ~available declarations
    in
    let domains, pending_domains =
      Program_declarations.take_declarations ~available domains
    in
    let workers, pending_workers =
      Program_declarations.take_declarations ~available workers
    in
    let fields, pending_fields =
      Program_declarations.take_declarations ~available fields
    in
    ( declarations @ domains @ workers @ fields,
      (pending_declarations, pending_domains, pending_workers, pending_fields) )
  in
  let instance_member ~at instance = Value_instances.member ~loc:at instance in
  let root_cells =
    List.filter_map state.tables.function_instances ~f:(fun instance ->
        if
          (not (List.is_empty instance.instance_namespace))
          || not (String.equal instance.instance_worker Prelude.cell_family)
        then None
        else
          let dependencies =
            List.concat_map instance.instance_arguments ~f:(fun argument ->
                Option.value
                  (List.find_map state.tables.dictionaries ~f:(fun request ->
                       Option.some_if
                         (Option.equal String.equal
                            (Datatypes.dictionary_name request.domain_types
                               request.domain_type)
                            (Some argument))
                         (domain_dependencies request)))
                  ~default:[])
          in
          Some (dependencies, [ instance_member ~at:R.Loc.none instance ]))
  in
  let ready_cells, deferred_cells =
    Program_declarations.take_declarations ~available:[] root_cells
  in
  let deferred_domains = deferred_domains @ deferred_cells in
  let imported_worker_members namespace =
    Option.value
      (List.Assoc.find library_worker_members
         (String.concat ~sep:"." namespace)
         ~equal:String.equal)
      ~default:[]
  in
  let support_instances =
    List.filter state.tables.function_instances ~f:(fun instance ->
        not
          (List.is_empty instance.instance_namespace
          && String.equal instance.instance_worker Prelude.cell_family))
  in
  let support_domains =
    List.filter value_domains ~f:(fun (name, _) ->
        (not (List.is_empty (Qualified_name.of_string name).path))
        || Set.mem family_domain_names name)
  in
  let namespaces =
    List.map support_domains ~f:(fun (name, _) -> (Qualified_name.of_string name).path)
    @ List.map support_instances ~f:(fun instance -> instance.instance_namespace)
    |> List.dedup_and_sort ~compare:(List.compare String.compare)
  in
  let domain_dependencies = Generic_support.domain_dependencies domain_requests in
  let* support_members =
    all namespaces ~f:(fun namespace ->
        let* members =
          Generic_support.order ~namespace ~at:Location.none ~domains:support_domains
            ~domain_dependencies ~instances:support_instances
        in
        Ok (namespace, members))
  in
  let rec emit_context_members ?namespace ?(library = false) destination ~at
      ~representations ~native_resources ~applications ~late_members =
    let namespace =
      Option.value namespace ~default:(Module_context.namespace destination)
    in
    let ghost_fields =
      List.concat_map view_fields ~f:(fun (_, view) ->
          let owner =
            match
              List.find generic_predicates ~f:(fun worker ->
                  String.is_prefix view.View_storage.field
                    ~prefix:(worker.Generic_parameters.name ^ "."))
            with
            | Some worker -> predicate_destination worker.key
            | None ->
                Program_structures.destination_of_group
                  (field_group view.View_storage.field)
          in
          if Module_context.same_destination owner destination then
            View_storage.members ~loc:at
              ~local_name:(Module_context.local_name destination)
              view
          else [])
    in
    let primitive_members =
      State.primitives_in state.tables namespace
      |> List.map ~f:(fun primitive -> primitive.State.member)
    in
    let defaults =
      List.filter_map state.tables.defaults ~f:(fun request ->
          Option.some_if
            (List.equal String.equal request.default_namespace namespace)
            (R.Member.free
               (R.Member.value ~loc:at ~typ:request.default_type
                  (ident ~loc:at (Qualified_name.of_string request.default_name).name)
                  None)))
    in
    let function_workers =
      List.filter callable_workers ~f:(fun worker ->
          List.equal String.equal (Qualified_name.of_string (callable_name worker)).path
            namespace
          && ((not (List.is_empty namespace))
             || List.is_empty (Map.find_exn worker_dependencies (callable_name worker))))
      |> List.map ~f:(emit_callable_worker destination)
    in
    let support =
      Option.value
        (List.Assoc.find support_members namespace ~equal:(List.equal String.equal))
        ~default:[]
    in
    let token_members =
      List.concat_map token_types ~f:(fun data ->
          match (data.Datatypes.family, data.atomic_procedure) with
          | Some family, Some procedure
            when List.equal String.equal namespace (String.split family.worker ~on:'.') ->
              let carrier =
                R.Type.atomic_token ~loc:at (qualified_name ~loc:at procedure)
              in
              [
                R.Member.type_ ~loc:at (ident ~loc:at family.member) (Some carrier);
                Prelude.value_dictionary ~loc:at ~name:family.dictionary ~carrier
                  ~unrestricted:(R.Expr.bool ~loc:at true)
                  ~body:(R.Expr.bool ~loc:at true);
              ]
          | _ -> [])
    in
    let family_resources =
      List.concat_map (generic_resource_workers @ generic_model_workers)
        ~f:(fun (worker, members) ->
          if
            List.equal String.equal namespace
              (String.split worker.Generic_parameters.name ~on:'.')
          then members
          else [])
    in
    let stages =
      if library then [ `Function_workers; `Value_domains; `Primitives; `Late_members ]
      else
        match destination with
        | Module_context.Flat ->
            [
              `Representations;
              `Definitions;
              `Native_resources;
              `Public_resources;
              `Function_workers;
              `Applications;
              `Value_domains;
              `View_fields;
              `Fields;
              `Proof_definitions;
              `State;
              `Late_members;
              `Primitives;
              `Predicates;
              `Pure_functions;
              `Lemmas;
              `Logical_functions;
              `Procedures;
            ]
        | Module_context.Worker _ ->
            [
              `Representations;
              `Definitions;
              `Native_resources;
              `Public_resources;
              `Applications;
              `Function_workers;
              `Value_domains;
              `Primitives;
              `Pure_functions;
              `Fields;
              `View_fields;
              `State;
              `Proof_definitions;
              `Late_members;
              `Predicates;
              `Lemmas;
              `Logical_functions;
              `Procedures;
            ]
        | Module_context.Function_worker _ | Module_context.Proof_worker _ ->
            [
              `Token_types;
              `Function_workers;
              `Value_domains;
              `Family_assets;
              `Primitives;
              `Fields;
              `View_fields;
              `State;
              `Predicates;
              `Logical_functions;
              `Lemmas;
              `Pure_functions;
              `Procedures;
            ]
    in
    List.concat_map stages ~f:(function
      | `Token_types -> token_members
      | `Family_assets -> family_resources
      | `Representations -> representations
      | `Definitions -> emitted_assets destination definition_modules
      | `Native_resources -> native_resources
      | `Public_resources -> emitted_assets destination public_resource_members
      | `Applications -> applications
      | `Function_workers -> function_workers
      | `Value_domains -> support @ defaults
      | `View_fields -> ghost_fields
      | `Fields -> emitted_fields destination explicit_fields
      | `Proof_definitions -> emitted_assets destination definition_proof_modules
      | `State ->
          state_members destination structure_member_lists
          @ state_members destination pending_member_lists
          @ state_members destination action_check_lists
      | `Late_members -> late_members
      | `Primitives -> primitive_members
      | `Predicates -> (
          List.map (emitted_predicates destination) ~f:R.Member.callable
          @
          match destination with
          | Module_context.Proof_worker _ -> imported_worker_members namespace
          | Flat | Worker _ | Function_worker _ -> [])
      | `Pure_functions ->
          List.map (owned destination pure_funcs) ~f:(fun (_, member) ->
              R.Member.callable member)
      | `Lemmas -> emitted_proofs destination proof_lemma_members
      | `Logical_functions -> emitted_proofs destination logical_members
      | `Procedures -> (
          List.map (owned destination procs) ~f:procedure_member
          @
          match destination with
          | Module_context.Function_worker _ -> imported_worker_members namespace
          | Flat | Worker _ | Proof_worker _ -> []))
  and emit_callable_worker parent = function
    | Proof_worker worker ->
        let destination = Module_context.Proof_worker (worker, parent) in
        let l = loc worker.loc in
        R.Member.module_ ~loc:l
          ~params:
            (List.mapi worker.variables ~f:(fun index _ ->
                 ( ident ~loc:l ("A" ^ Int.to_string index),
                   qualified_name ~loc:l Prelude.value_interface )))
          (ident ~loc:l (Qualified_name.of_string worker.name).name)
          (emit_context_members destination ~at:l ~representations:[] ~native_resources:[]
             ~applications:[] ~late_members:[])
    | Runtime_worker worker ->
        let destination = Module_context.Function_worker (worker, parent) in
        let l = loc worker.loc in
        let value_interface = qualified_name ~loc:l Prelude.value_interface in
        let parameter index = "A" ^ Int.to_string index in
        (* A witness worker takes the witness, whose dictionaries its variables are. *)
        let params, witness_members =
          match worker.witness with
          | None ->
              ( List.mapi worker.scheme.variables ~f:(fun index _ ->
                    (ident ~loc:l (parameter index), value_interface)),
                [] )
          | Some witness ->
              ( (ident ~loc:l "W", qualified_name ~loc:l witness.interface)
                :: List.filter_mapi witness.members ~f:(fun index member ->
                    Option.some_if (Option.is_none member)
                      (ident ~loc:l (parameter index), value_interface)),
                List.filter_mapi witness.members ~f:(fun index member ->
                    Option.map member ~f:(fun position ->
                        R.Member.alias ~loc:l ~typ:value_interface
                          (ident ~loc:l (parameter index))
                          (qualified_name ~loc:l ("W." ^ parameter position)))) )
        in
        R.Member.module_ ~loc:l ~params
          (ident ~loc:l (Qualified_name.of_string worker.name).name)
          (witness_members
          @ emit_context_members destination ~at:l ~representations:[]
              ~native_resources:[] ~applications:[] ~late_members:[])
  in
  let deferred_function_workers =
    List.filter_map root_callable_workers ~f:(fun worker ->
        let dependencies = Map.find_exn worker_dependencies (callable_name worker) in
        if List.is_empty dependencies then None
        else Some (dependencies, [ emit_callable_worker Module_context.Flat worker ]))
  in
  let library_modules =
    List.map library_parts ~f:(fun (library, members) ->
        let l = loc library.Library_modules.library.scope.location in
        R.Member.module_ ~loc:l
          (ident ~loc:l library.library_name)
          (emit_context_members ~namespace:[ library.library_name ] ~library:true
             Module_context.Flat ~at:l ~representations:[] ~native_resources:[]
             ~applications:[] ~late_members:members))
  in
  let dictionary_for ~at binding id =
    let concrete = checked_raw_types types binding in
    Report.expect ~at
      ("The value dictionary of type " ^ Ident.name id)
      (Datatypes.dictionary_name concrete (Ctype.newconstr (Path.Pident id) []))
  in
  let* paired_generics =
    Report.zip ~at:Location.none "The generic module groups and their interfaces" generics
      generic_interfaces
  in
  (* The exceptions of functor bodies their applications share: each application's own
     are given by a module. *)
  let* shared_exception_members =
    all generics ~f:(fun group ->
        Result.map
          (Exceptions.shared_members
             ~loc:(loc group.representative.template.mod_loc)
             types group)
          ~f:(fun members -> (group, members)))
  in
  let shared_exception_modules group =
    Option.join (List.Assoc.find shared_exception_members group ~equal:phys_equal)
  in
  let* generic_implementation_templates =
    all paired_generics ~f:(fun (group, interface) ->
        let l = loc group.representative.template.mod_loc in
        let q = qualified_name ~loc:l in
        let* ra_data =
          all
            (List.filter_map private_ra_types ~f:(fun (plan, data) ->
                 Option.some_if (phys_equal plan.Generic_proofs.group group) data))
            ~f:(Datatypes.member types)
        in
        let destination = Module_context.Worker group in
        let native_resources =
          List.filter_map native_resource_members ~f:(fun (backend, member) ->
              Option.bind
                (List.find source.proof_resources ~f:(fun resource ->
                     String.equal backend resource.Source.resource_backend))
                ~f:(fun resource ->
                  Option.some_if
                    (Module_context.emits_owner module_contexts ~destination
                       resource.resource_scope)
                    member))
        in
        let members =
          emit_context_members destination ~at:l ~representations:ra_data
            ~native_resources ~applications:[] ~late_members:[]
        in
        let worker =
          R.Member.module_ ~loc:l
            ~params:
              (List.map (Generic_modules.parameter_groups group) ~f:(fun stage ->
                   (ident ~loc:l stage.parameter, q stage.interface))
              @ (if Option.is_some group.world then
                   [
                     (ident ~loc:l "Layout", q (Option.value_exn group.world ^ ".Shape"));
                   ]
                 else [])
              @
              if Option.is_some (shared_exception_modules group) then
                [ (ident ~loc:l "App", q (Exceptions.shared_interface group)) ]
              else [])
            (ident ~loc:l (Qualified_name.of_string group.name).name)
            members
        in
        match group.world with
        | None -> Ok (worker, [], [])
        | Some world ->
            let* layout_types =
              Result_layouts.symbolic layouts group ~owner:[ world; "Shape" ]
            in
            let proof_plan =
              List.find generic_proofs ~f:(fun plan ->
                  phys_equal plan.Generic_proofs.group group)
            in
            let model_types =
              Option.value_map proof_plan ~default:[] ~f:(fun plan ->
                  Generic_proofs.symbolic_models source plan ~owner:[ world; "Shape" ]
                  |> List.filter ~f:(fun data ->
                      not (Generic_models.dependent types data)))
            in
            let parameter_types =
              Option.value_map proof_plan ~default:[] ~f:(fun plan ->
                  Generic_proofs.parameter_types ~world:true plan ~owner:(fun _ ->
                      [ world ]))
            in
            let layout_types = layout_types @ model_types in
            let environment =
              layout_types @ parameter_types
              @ List.concat_map (Generic_modules.parameter_groups group) ~f:(fun stage ->
                  Generic_modules.world_types stage ~owner:[ world ])
              @ types
            in
            let* data_members =
              all
                (List.filter layout_types ~f:(fun d -> Option.is_none d.Datatypes.heap))
                ~f:(Datatypes.member environment)
            in
            let* family_parts =
              all layout_types ~f:(Datatypes.value_family_members environment)
            in
            let family_members =
              Datatypes.unique_domain_members (List.concat_map family_parts ~f:fst)
            in
            let family_templates = List.concat_map family_parts ~f:snd in
            let* fields =
              all
                (List.concat_map layout_types ~f:(fun d ->
                     List.map (Option.value d.Datatypes.heap ~default:[]) ~f:(fun field ->
                         (d, field))))
                ~f:(fun (d, field) ->
                  let* typ =
                    Datatypes.typ environment ~at:d.Datatypes.at field.Datatypes.typ
                  in
                  let leaf = (Qualified_name.of_string field.raven_field).name in
                  Ok (Datatypes.field_member environment ~loc:l leaf typ field.typ))
            in
            let projection =
              Option.value_map proof_plan ~default:Subst.identity
                ~f:Generic_proofs.projection
            in
            let field_contexts =
              (String.split group.name ~on:'.' @ [ "Layout" ], projection)
              :: List.map group.applications ~f:(fun application ->
                  let substitution =
                    List.fold application.source.declarations ~init:projection
                      ~f:(fun substitution declaration ->
                        match
                          Generic_proofs.matching_type declaration
                            group.representative.declarations
                        with
                        | Some target
                          when not (Ident.same declaration.typ_id target.typ_id) ->
                            Subst.add_type declaration.typ_id (Path.Pident target.typ_id)
                              substitution
                        | Some _ | None -> substitution)
                  in
                  ([ application.layout ], substitution))
            in
            let cell_environment =
              List.map layout_types ~f:(fun data ->
                  let aliases =
                    List.concat_map types ~f:(fun candidate ->
                        let same_namespace =
                          Option.exists candidate.Datatypes.cell_namespace
                            ~f:(fun owner ->
                              List.Assoc.mem field_contexts owner
                                ~equal:(List.equal String.equal))
                        in
                        let same_name =
                          Option.exists candidate.module_path ~f:(fun path ->
                              Option.equal String.equal (List.last path)
                                (Some data.Datatypes.module_name))
                        in
                        if same_namespace && same_name then
                          candidate.paths
                          @ Option.to_list
                              (Option.map candidate.id ~f:(fun id -> Path.Pident id))
                        else [])
                  in
                  Datatypes.with_paths data aliases)
              @ environment
            in
            let cell_payloads =
              List.filter_map state.tables.dictionaries ~f:(fun request ->
                  Option.bind
                    (Datatypes.domain_namespace request.domain_types request.domain_type)
                    ~f:(fun namespace ->
                      Option.map
                        (List.Assoc.find field_contexts namespace
                           ~equal:(List.equal String.equal))
                        ~f:(fun substitution ->
                          Subst.type_expr substitution request.domain_type)))
            in
            let* layout_domain_members, layout_templates =
              let rebase typ = Subst.type_expr projection typ in
              let layout_roots =
                List.concat_map layout_types ~f:(fun data ->
                    let own =
                      if not (List.is_empty data.Datatypes.parameters) then []
                      else
                        Option.to_list
                          (Option.map data.Datatypes.id ~f:(fun id ->
                               Ctype.newconstr (Path.Pident id) []))
                    in
                    own
                    @ List.map (Option.value data.heap ~default:[]) ~f:(fun field ->
                        field.Datatypes.typ))
                @ cell_payloads
              in
              let requests =
                List.filter_map domain_requests ~f:(fun request ->
                    Option.bind
                      (Datatypes.domain_namespace request.domain_types request.domain_type)
                      ~f:(fun namespace ->
                        Option.map
                          (List.Assoc.find field_contexts namespace
                             ~equal:(List.equal String.equal))
                          ~f:(fun substitution ->
                            Subst.type_expr substitution request.domain_type)))
              in
              let requested = List.map layout_roots ~f:rebase @ requests in
              let* members =
                Datatypes.domain_members ~dictionaries:true cell_environment requested
              in
              Ok
                ( members,
                  Datatypes.value_templates ~dictionaries:true cell_environment requested
                )
            in
            let layout_domains =
              List.filter_map layout_domain_members ~f:(fun (name, member) ->
                  Option.some_if
                    (List.equal String.equal (Qualified_name.of_string name).path
                       [ world; "Shape" ])
                    member)
            in
            let world_domains =
              Datatypes.unique_domain_members
                (List.filter_map (family_members @ layout_domain_members)
                   ~f:(fun (name, member) ->
                     Option.some_if
                       (List.equal String.equal (Qualified_name.of_string name).path
                          [ world ])
                       (name, member))
                @ List.filter_map value_domains ~f:(fun (name, member) ->
                    Option.some_if
                      (List.equal String.equal (Qualified_name.of_string name).path
                         [ world ])
                      (name, member)))
              |> List.map ~f:snd
            in
            let shape =
              R.Member.module_ ~loc:l ~interface:true (ident ~loc:l "Shape")
                (data_members
                @ List.filter_map family_members ~f:(fun (name, member) ->
                    Option.some_if
                      (List.equal String.equal (Qualified_name.of_string name).path
                         [ world; "Shape" ])
                      member)
                @ layout_domains @ fields)
            in
            let factory =
              R.Member.unit_factory ~loc:l
                ~implements:[ (q (world ^ ".Shape"), []) ]
                (ident ~loc:l "Fresh") []
            in
            Ok
              ( R.Member.module_ ~loc:l
                  ~params:
                    (List.map (Generic_modules.type_slots group) ~f:(fun stem ->
                         ( ident ~loc:l stem,
                           qualified_name ~loc:l
                             (Generic_modules.type_slot_interface group stem) )))
                  (ident ~loc:l world)
                  (world_domains @ interface @ [ shape; factory; worker ]),
                family_templates @ layout_templates,
                List.filter family_members ~f:(fun (name, _) ->
                    List.is_empty (Qualified_name.of_string name).path) ))
  in
  let generic_implementations =
    List.map generic_implementation_templates ~f:(fun (members, _, _) -> members)
  in
  let layout_templates =
    List.map generic_implementation_templates ~f:(fun (_, templates, _) -> templates)
  in
  let value_factories =
    Datatypes.unique_domain_members
      (List.concat_map value_family_parts ~f:fst
      @ List.concat_map generic_implementation_templates ~f:(fun (_, _, dependencies) ->
          dependencies))
    |> List.filter_map ~f:(fun (name, member) ->
        Option.some_if
          (not (List.Assoc.mem value_domains name ~equal:String.equal))
          member)
  in
  let value_templates =
    ordinary_value_templates @ value_factory_templates @ List.concat layout_templates
  in
  let needs_template template = List.mem value_templates template ~equal:Poly.equal in
  let tuple_arities =
    List.filter_map value_templates ~f:(function
      | Datatypes.Tuple_dictionary arity -> Some arity
      | Int_dictionary | List_dictionary | Option_dictionary -> None)
    |> List.dedup_and_sort ~compare:Int.compare
  in
  let* generic_instances =
    all generics ~f:(fun group ->
        all group.applications ~f:(fun application ->
            let views =
              List.map application.source.parameters ~f:(fun parameter ->
                  List.find_exn checked_modules ~f:(fun view ->
                      phys_equal view.Checked_modules.binding
                        parameter.Module_inventory.argument))
            in
            let view_names = List.map views ~f:(fun view -> view.Checked_modules.name) in
            let l = loc application.source.argument.site.item_loc in
            let q = qualified_name ~loc:l in
            let* setup, worker, arguments =
              match group.world with
              | None -> Ok ([], group.name, view_names)
              | Some world ->
                  let canonical =
                    List.find_exn group.applications ~f:(fun other ->
                        Path.same other.source.identity application.source.identity)
                  in
                  let* arguments =
                    all application.source.parameters ~f:(fun parameter ->
                        let concrete =
                          checked_raw_types types parameter.Module_inventory.argument
                        in
                        all
                          (List.filter parameter.argument.expected.signature_types
                             ~f:(fun (_, declaration) ->
                               not (Generic_type_families.transparent declaration)))
                          ~f:(fun (member, declaration) ->
                            let t =
                              Btype.newgenty
                                (Tconstr
                                   ( Path.Pident declaration.Typedtree.typ_id,
                                     [],
                                     ref Types.Mnil ))
                            in
                            if
                              Option.is_none declaration.typ_manifest
                              && Generic_type_families.arity declaration > 0
                            then
                              let stage =
                                List.find_exn (Generic_modules.parameter_groups group)
                                  ~f:(fun stage ->
                                    Ident.same stage.representative.parameter
                                      parameter.parameter)
                              in
                              let stem =
                                List.Assoc.find_exn stage.types member ~equal:String.equal
                              in
                              Ok
                                (R.Type.named ~loc:l
                                   (q
                                      (Generic_type_families.factory_name
                                         ~world:canonical.world ~member:stem))
                                   [])
                            else if Option.is_none declaration.typ_manifest then
                              Result.map
                                (dictionary_for ~at:declaration.typ_loc parameter.argument
                                   declaration.typ_id) ~f:(fun dictionary ->
                                  R.Type.named ~loc:l (q dictionary) [])
                            else Datatypes.typ concrete ~at:declaration.typ_loc t)
                        |> Result.bind ~f:(fun ordinary ->
                            all parameter.argument.expected.signature_ghost_modules
                              ~f:(fun (_, formal) ->
                                let resource = formal.Module_inventory.ghost_resource in
                                Datatypes.typ concrete ~at:resource.resource_at
                                  resource.resource_type)
                            |> Result.map ~f:(fun carriers -> ordinary @ carriers)))
                    |> Result.map ~f:List.concat
                  in
                  let selected =
                    if List.is_empty (Generic_modules.type_slots group) then
                      R.Member.alias ~loc:l (ident ~loc:l application.world) (q world)
                    else
                      R.Member.instance ~loc:l
                        ~def:(q world, arguments)
                        (ident ~loc:l application.world)
                        (q world)
                  in
                  let fresh =
                    if phys_equal canonical application then
                      [
                        R.Member.unit_instance ~loc:l
                          (ident ~loc:l canonical.layout)
                          (q (application.world ^ ".Fresh"));
                      ]
                    else []
                  in
                  let factories =
                    if phys_equal canonical application then
                      List.concat_map type_constructor_factories
                        ~f:(fun (binding, members) ->
                          if phys_equal binding application.source.argument then members
                          else [])
                    else []
                  in
                  Ok
                    ( factories @ (selected :: fresh),
                      application.world ^ "." ^ (Qualified_name.of_string group.name).name,
                      view_names @ [ canonical.layout ] )
            in
            let exception_module, arguments =
              match shared_exception_modules group with
              | Some (_, modules) ->
                  ( [ List.Assoc.find_exn modules application ~equal:phys_equal ],
                    arguments @ [ Exceptions.shared_module application ] )
              | None -> ([], arguments)
            in
            Ok
              ( application.source.argument,
                setup @ exception_module,
                R.Member.instance ~loc:l
                  ~def:
                    ( q worker,
                      List.map arguments ~f:(fun n -> R.Type.named ~loc:l (q n) []) )
                  (ident ~loc:l application.name)
                  (q worker) )))
  in
  let generic_instances = List.concat generic_instances in
  (* The modules of the checked bindings, each followed by the declarations that the layouts
     it makes available let through. *)
  let* checked_pairs =
    Report.zip ~at:Location.none "The checked modules and their members" checked_modules
      checked_module_members
  in
  let checked_module ~what binding =
    Report.expect ~at:Location.none what
      (List.find checked_pairs ~f:(fun (view, _) ->
           phys_equal view.Checked_modules.binding binding))
  in
  let* _, native_blocks, pending, _ =
    List.fold_result checked_pairs
      ~init:
        ( [],
          [],
          ( pending_declarations,
            deferred_domains,
            deferred_function_workers,
            pending_fields ),
          [] )
      ~f:(fun (emitted, blocks, pending, available) (view, members) ->
        let binding = view.Checked_modules.binding in
        if deferred_native_binding binding then Ok (emitted, blocks, pending, available)
        else
          let attached =
            List.concat_map generics ~f:(fun group ->
                List.concat_map group.Generic_modules.applications ~f:(fun application ->
                    if not (phys_equal application.source.argument binding) then []
                    else
                      List.filter_map (List.drop_last_exn application.source.parameters)
                        ~f:(fun parameter ->
                          let argument = parameter.Module_inventory.argument in
                          Option.some_if
                            (not (List.mem emitted argument ~equal:phys_equal))
                            argument)))
          in
          let rec attach (emitted, attached) argument =
            if List.mem emitted argument ~equal:phys_equal then Ok (emitted, attached)
            else
              let* view, _ =
                checked_module ~what:"The checked module of a functor argument" argument
              in
              let dependency =
                Option.bind view.target ~f:(fun target ->
                    List.find checked_modules ~f:(fun candidate ->
                        String.equal candidate.Checked_modules.name target))
              in
              let* emitted, attached =
                match dependency with
                | None -> Ok (emitted, attached)
                | Some dependency -> attach (emitted, attached) dependency.binding
              in
              Ok (argument :: emitted, argument :: attached)
          in
          let* _, attached = List.fold_result attached ~init:(emitted, []) ~f:attach in
          let attached = List.rev attached in
          let* attached_views =
            all attached
              ~f:(checked_module ~what:"The checked module of a functor argument")
          in
          let attached_members = List.concat_map attached_views ~f:snd in
          let prefix =
            List.concat_map (List.zip_exn paired_generics generic_implementations)
              ~f:(fun ((group, interface), implementation) ->
                if phys_equal group.representative.argument binding then
                  match group.Generic_modules.world with
                  | None -> interface @ [ implementation ]
                  | Some _ -> [ implementation ]
                else [])
          in
          let before_setup, pending = take_available ~available pending in
          let instances =
            List.filter_map generic_instances ~f:(fun (argument, _, instance) ->
                Option.some_if (phys_equal argument binding) instance)
          in
          let publications =
            List.filter_map publication_members ~f:(fun (owner, member) ->
                Option.some_if
                  (phys_equal owner binding || List.mem attached owner ~equal:phys_equal)
                  (R.Member.callable member))
          in
          let setup =
            List.concat_map generic_instances ~f:(fun (argument, setup, _) ->
                if phys_equal argument binding then setup else [])
          in
          let make_available available select =
            List.fold generics ~init:available ~f:(fun available group ->
                List.fold group.Generic_modules.applications ~init:available
                  ~f:(fun available application ->
                    Option.value_map (select group application) ~default:available
                      ~f:(fun layout -> layout :: available)))
          in
          let available =
            make_available available (fun group application ->
                Option.some_if
                  (phys_equal application.source.argument binding
                  && Option.is_some group.world)
                  application.layout)
          in
          let declarations, pending = take_available ~available pending in
          let available =
            make_available available (fun _ application ->
                Option.some_if
                  (phys_equal application.source.argument binding)
                  application.name)
          in
          let available =
            view.name
            :: List.fold attached_views ~init:available ~f:(fun available (view, _) ->
                view.Checked_modules.name :: available)
          in
          let after_instances, pending = take_available ~available pending in
          Ok
            ( (binding :: attached) @ emitted,
              (before_setup @ prefix @ setup @ declarations @ publications
             @ attached_members @ members @ instances @ after_instances)
              :: blocks,
              pending,
              available ))
  in
  let native_modules = List.concat (List.rev native_blocks) in
  let pending_declarations, pending_domains, pending_workers, pending_fields = pending in

  let file_start = { Lexing.dummy_pos with pos_fname = source.file } in
  let start = R.Loc.make file_start file_start in
  let root_members =
    emit_context_members Module_context.Flat ~at:start ~representations:[]
      ~native_resources:deferred_native_resource_members ~applications:native_modules
      ~late_members:
        (List.concat_map
           (pending_declarations @ pending_domains @ pending_workers @ pending_fields)
           ~f:snd)
  in
  Ok
    ( R.Program.make ~loc:start
        (Prelude.members
        @ List.map
            (List.concat_map generics ~f:(fun group ->
                 List.concat_map (Generic_modules.parameter_groups group) ~f:(fun stage ->
                     List.filter_map
                       stage.representative.argument.expected.signature_types
                       ~f:(fun (_, declaration) ->
                         let count = Generic_type_families.arity declaration in
                         Option.some_if
                           (Option.is_none declaration.typ_manifest && count > 0)
                           count)))
            |> List.dedup_and_sort ~compare:Int.compare)
            ~f:Generic_type_families.signature
        @ Prelude.value_functors
            ~integers:(needs_template Datatypes.Int_dictionary)
            ~lists:(needs_template Datatypes.List_dictionary)
            ~options:(needs_template Datatypes.Option_dictionary)
            ~tuple_arities ()
        @ (if
             List.exists state.tables.function_instances ~f:(fun instance ->
                 String.equal instance.instance_worker Prelude.cell_family)
           then Prelude.cell_members
           else [])
        @ (if state.tables.dynamic_indices then Indexed_initialization.members else [])
        @ (if List.exists structure_member_lists ~f:(fun (st, _) -> has_history st) then
             History.program_members history
           else [])
        @ imported_resource_members @ modules @ value_factories
        @ List.filter_map shared_exception_members ~f:(fun (_, members) ->
            Option.map members ~f:fst)
        @ ready_domains @ ready_cells @ fields @ library_modules @ root_members),
      state.origins,
      List.rev state.warnings )

let program ?history source =
  let* program, origins, warnings = program_with_diagnostics ?history source in
  List.iter warnings ~f:Report.print_diagnostic;
  Ok (program, origins)
