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
let program ?(history = History.default) (source : Source.t) :
    (R.Program.t * origin list, error) Result.t =
  let* scopes = Program_scopes.run source in
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
  let* decls = Program_declarations.run scopes in
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
  let* proofs, state = Program_proofs.run scopes decls State.initial in
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
  let* shaped = Program_structures.run ~history scopes decls proofs in
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
  let* translated, state = Program_members.run scopes decls proofs shaped state in
  let {
    Program_members.library_modules = library_parts;
    library_worker_members;
    publication_members;
    generic_interfaces;
    checked_module_members;
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
    List.filter_map predicate_members ~f:(fun (key, member) ->
        Option.some_if
          (Module_context.same_destination destination (predicate_destination key))
          member)
  in
  let proof_lemma_members =
    List.zip_exn
      (List.map lemma_declarations ~f:(fun d -> (Proof_scopes.name d).pid_str))
      lemma_members
  in
  let logical_members =
    List.zip_exn
      (List.map logical_declarations ~f:(fun d -> (Proof_scopes.name d).pid_str))
      logical_members
  in
  let proof_members =
    List.map (predicate_members @ proof_lemma_members) ~f:(fun (name, member) ->
        (name, R.Member.callable member))
    @ logical_members
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
          List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
              Option.bind
                (List.find scoped_proofs.bindings ~f:(fun binding ->
                     Ident.same binding.entry.id entry.id
                     && (match binding.kind with Function _ -> true | _ -> false)
                     && Option.exists (definition_resource binding.entry.scope)
                          ~f:(fun owner ->
                            Ident.same owner.resource_id resource.resource_id)))
                ~f:(fun binding ->
                  List.Assoc.find proof_members binding.backend ~equal:String.equal))
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
                List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
                    Option.bind
                      (List.find scoped_proofs.bindings ~f:(fun binding ->
                           Ident.same binding.entry.id entry.id
                           && (match binding.kind with
                             | Predicate _ | Lemma _ -> true
                             | _ -> false)
                           && Option.exists (definition_resource binding.entry.scope)
                                ~f:(fun owner ->
                                  Ident.same owner.resource_id resource.resource_id)))
                      ~f:(fun binding ->
                        List.Assoc.find proof_members binding.backend ~equal:String.equal))
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
  let emitted_fields destination fields =
    List.filter_map fields ~f:(fun (field, member) ->
        Option.some_if
          (Module_context.emits_owner module_contexts ~destination
             field.Source.field_scope)
          member)
  in
  let raw_resource_field field =
    Option.is_some field.Source.field_resource
    || List.exists all_resource_views ~f:(fun resource ->
        resource.Source.resource_is_ra
        && same_named_type field.field_value resource.resource_type)
  in
  let* explicit_fields =
    all source.proof_fields ~f:(fun field ->
        let l = loc field.Source.field_at in
        let* value_type =
          match field.field_resource with
          | None ->
              begin match
                List.find all_resource_views ~f:(fun resource ->
                    resource.resource_is_ra
                    && same_named_type field.field_value resource.resource_type)
              with
              | None -> Datatypes.typ types ~at:field.field_at field.field_value
              | Some resource ->
                  Ok
                    (R.Type.named ~loc:l
                       (qualified_name ~loc:l resource.resource_backend)
                       [])
              end
          | Some owner ->
              begin match
                List.find all_resource_views ~f:(fun resource ->
                    Source.resource_has_path resource owner)
              with
              | None -> error field.field_at "Unknown resource algebra for field"
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
                          error field.field_at "Missing resource algebra implementation"
                    else Ok resource.resource_backend
                  in
                  if resource.resource_is_ra then
                    Ok (R.Type.named ~loc:l (qualified_name ~loc:l backend) [])
                  else error field.field_at "The field resource is not a resource algebra"
              end
        in
        Ok
          ( field,
            let field_name = (Qualified_name.of_string (ghost_field_name field)).name in
            if raw_resource_field field then
              R.Member.field ~ghost:true ~loc:l (ident ~loc:l field_name) value_type
            else
              Datatypes.field_member ~ghost:true types ~loc:l field_name value_type
                field.field_value ))
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
                         (Option.is_none declaration.Typedtree.typ_manifest)
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
  let value_domains =
    Datatypes.unique_domain_members (List.concat_map domain_groups ~f:snd)
  in
  let ordinary_value_templates =
    List.concat_map registered_domains ~f:(fun request ->
        Datatypes.value_templates request.domain_types [ request.domain_type ])
    @ List.concat_map argument_domains ~f:(fun request ->
        Datatypes.value_templates ~dictionaries:true request.domain_types
          [ request.domain_type ])
    @ Datatypes.value_templates types field_domain_types
  in
  let root_domain_declarations =
    List.filter_map value_domains ~f:(fun (name, member) ->
        Option.some_if
          (List.is_empty (Qualified_name.of_string name).path)
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
    List.map (generic_predicate_workers @ generic_callables) ~f:(fun worker ->
        Proof_worker worker)
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
  let domains_in namespace =
    if List.is_empty namespace then []
    else
      List.filter_map value_domains ~f:(fun (name, member) ->
          Option.some_if
            (List.equal String.equal (Qualified_name.of_string name).path namespace)
            member)
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
    let domains = domains_in namespace in
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
    let function_instances =
      List.filter_map state.tables.function_instances ~f:(fun instance ->
          Option.some_if
            (List.equal String.equal instance.instance_namespace namespace
            && not
                 (List.is_empty namespace
                 && String.equal instance.instance_worker Prelude.cell_family))
            (instance_member ~at instance))
    in
    let stages =
      if library then
        [
          `Value_domains;
          `Function_workers;
          `Function_instances;
          `Primitives;
          `Late_members;
        ]
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
              `Function_instances;
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
              `Value_domains;
              `Function_workers;
              `Function_instances;
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
        | Module_context.Function_worker _ ->
            [
              `Value_domains;
              `Function_workers;
              `Function_instances;
              `Primitives;
              `Pure_functions;
              `Procedures;
            ]
        | Module_context.Proof_worker _ ->
            [
              `Value_domains;
              `Function_instances;
              `Primitives;
              `View_fields;
              `State;
              `Predicates;
              `Logical_functions;
              `Lemmas;
            ]
    in
    List.concat_map stages ~f:(function
      | `Representations -> representations
      | `Definitions -> emitted_assets destination definition_modules
      | `Native_resources -> native_resources
      | `Public_resources -> emitted_assets destination public_resource_members
      | `Applications -> applications
      | `Function_workers -> function_workers
      | `Function_instances -> function_instances
      | `Value_domains -> domains @ defaults
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
      | `Lemmas ->
          List.map (emitted_proofs destination proof_lemma_members) ~f:R.Member.callable
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
        R.Member.module_ ~loc:l
          ~params:
            (List.mapi worker.scheme.variables ~f:(fun index _ ->
                 ( ident ~loc:l ("A" ^ Int.to_string index),
                   qualified_name ~loc:l Prelude.value_interface )))
          (ident ~loc:l (Qualified_name.of_string worker.name).name)
          (emit_context_members destination ~at:l ~representations:[] ~native_resources:[]
             ~applications:[] ~late_members:[])
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
  let value_factory_templates = List.concat_map value_family_parts ~f:snd in
  let dictionary_for binding id =
    let concrete = checked_raw_types types binding in
    Option.value_exn
      (Datatypes.dictionary_name concrete (Ctype.newconstr (Path.Pident id) []))
  in
  let* generic_implementation_templates =
    all generics ~f:(fun group ->
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
              @
              if Option.is_some group.world then
                [ (ident ~loc:l "Layout", q (Option.value_exn group.world ^ ".Shape")) ]
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
                  Generic_proofs.symbolic_models source plan ~owner:[ world; "Shape" ])
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
                             (if
                                List.mem
                                  (Generic_modules.value_type_slots group)
                                  stem ~equal:String.equal
                              then Prelude.value_interface
                              else "Library.Type") )))
                  (ident ~loc:l world)
                  (world_domains
                  @ List.nth_exn generic_interfaces
                      (List.findi_exn generics ~f:(fun _ candidate ->
                           phys_equal candidate group)
                      |> fst)
                  @ [ shape; factory; worker ]),
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
                  let* arguments =
                    all application.source.parameters ~f:(fun parameter ->
                        let concrete =
                          checked_raw_types types parameter.Module_inventory.argument
                        in
                        all parameter.argument.expected.signature_types
                          ~f:(fun (_, declaration) ->
                            let t =
                              Btype.newgenty
                                (Tconstr
                                   ( Path.Pident declaration.Typedtree.typ_id,
                                     [],
                                     ref Types.Mnil ))
                            in
                            if Option.is_none declaration.typ_manifest then
                              Ok
                                (R.Type.named ~loc:l
                                   (q
                                      (dictionary_for parameter.argument
                                         declaration.typ_id))
                                   [])
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
                  let canonical =
                    List.find_exn group.applications ~f:(fun other ->
                        Path.same other.source.identity application.source.identity)
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
                  Ok
                    ( selected :: fresh,
                      application.world ^ "." ^ (Qualified_name.of_string group.name).name,
                      view_names @ [ canonical.layout ] )
            in
            Ok
              ( application.source.argument,
                setup,
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
  let _, native_blocks, pending, _ =
    List.fold
      (List.zip_exn checked_modules checked_module_members)
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
        if deferred_native_binding binding then (emitted, blocks, pending, available)
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
            if List.mem emitted argument ~equal:phys_equal then (emitted, attached)
            else
              let view =
                List.find_exn checked_modules ~f:(fun view ->
                    phys_equal view.Checked_modules.binding argument)
              in
              let dependency =
                Option.bind view.target ~f:(fun target ->
                    List.find checked_modules ~f:(fun candidate ->
                        String.equal candidate.Checked_modules.name target))
              in
              let emitted, attached =
                Option.value_map dependency ~default:(emitted, attached)
                  ~f:(fun dependency -> attach (emitted, attached) dependency.binding)
              in
              (argument :: emitted, argument :: attached)
          in
          let _, attached = List.fold attached ~init:(emitted, []) ~f:attach in
          let attached = List.rev attached in
          let attached_members =
            List.concat_map attached ~f:(fun argument ->
                snd
                  (List.find_exn (List.zip_exn checked_modules checked_module_members)
                     ~f:(fun (view, _) ->
                       phys_equal view.Checked_modules.binding argument)))
          in
          let prefix =
            List.concat_map
              (List.zip_exn generics
                 (List.zip_exn generic_interfaces generic_implementations))
              ~f:(fun (group, (interface, implementation)) ->
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
            :: List.fold attached ~init:available ~f:(fun available binding ->
                let view =
                  List.find_exn checked_modules ~f:(fun view ->
                      phys_equal view.Checked_modules.binding binding)
                in
                view.name :: available)
          in
          let after_instances, pending = take_available ~available pending in
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
        @ imported_resource_members @ modules @ value_factories @ ready_domains
        @ ready_cells @ fields @ library_modules @ root_members),
      state.origins )
