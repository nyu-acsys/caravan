(** The translation of OCaml implementations to Raven programs.

    So far: top-level functions on integers, booleans, unit, tuples and variant types,
    with their contracts. A function becomes a procedure, and a variant type a data type
    (see {!Datatypes}). Expressions are put in A-normal form, since a call is a statement
    in Raven; arguments are evaluated right to left, as OCaml does. *)

open Base
open Translate_context
open Procedures
open Program_items

let program (source : Source.t) : (R.Program.t * origin list, error) Result.t =
  let* scopes = Program_scopes.run source in
  let {
    Program_scopes.annotations;
    linearizations;
    initializations;
    fresh;
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
    available_layouts;
    modules;
    refs;
    primitives;
    functions;
    lifted;
    origins;
    ocaml_env;
    scoped_proofs;
    scoped_inputs;
    predicates;
    library_preds;
    procedures;
    generic_procedures;
  } =
    decls
  in
  let body_destination =
    Program_declarations.body_destination ~generics:scopes.generics
      ~module_contexts:scopes.module_contexts
      ~context_for_group:
        (Program_scopes.context_for_group ~module_contexts:scopes.module_contexts)
  in
  let take_declarations =
    Program_declarations.take_declarations
      ~pending_declarations:decls.pending_declarations
      ~available_layouts:decls.available_layouts
  in
  let* proofs = Program_proofs.run scopes decls in
  let {
    Program_proofs.checked_views;
    checked_resource_entries;
    logical_declarations;
    all_logical_functions;
    proof_support;
    preds;
    spec_funcs;
    lemma_declarations;
    lemma_context;
    module_parameters;
    private_scoped_inputs;
  } =
    proofs
  in
  let* shaped = Program_structures.run scopes decls proofs in
  let {
    Program_structures.structures;
    structure_member_lists;
    view_fields;
    shared;
    generic_shared;
    past_structures;
    pasts;
    past_returns;
    ghost_args;
  } =
    shaped
  in
  let owner_destination =
    Program_structures.owner_destination
      ~declaration_context:
        (Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
           ~unapplied_proofs:scopes.unapplied_proofs)
  in
  let same_group = Program_structures.same_group in
  let field_group = Program_structures.field_group ~generics:scopes.generics in
  let state_members =
    Program_structures.state_members
      ~declaration_context:
        (Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
           ~unapplied_proofs:scopes.unapplied_proofs)
  in
  let* translated = Program_members.run scopes decls proofs shaped in
  let {
    Program_members.library_modules;
    publication_members;
    generic_interfaces;
    checked_module_members;
    action_check_lists;
    pending_member_lists;
    pred_members;
    lemma_members;
    logical_members;
    runtime_primitives;
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
  let emitted_proofs destination members =
    List.filter_map members ~f:(fun (name, member) ->
        Option.some_if
          (Module_context.same_destination (owner_destination name) destination
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
            Datatypes.field_member ~ghost:true types ~loc:l
              (Qualified_name.of_string (ghost_field_name field)).name value_type
              field.field_value ))
  in
  let emit_context_members destination ~at ~representations ~native_resources
      ~applications ~late_members =
    let group = List.hd (Module_context.groups destination) in
    let ghost_fields =
      List.filter_map view_fields ~f:(fun (_, (field, typ, init)) ->
          Option.some_if
            (Option.is_none init && same_group (field_group field) group)
            (R.Member.field ~loc:at ~ghost:true
               (ident ~loc:at (Module_context.local_name destination field))
               typ))
    in
    let primitive_members =
      !(List.Assoc.find_exn runtime_primitives destination
          ~equal:Module_context.same_destination)
      |> List.map ~f:snd
    in
    let stages =
      match destination with
      | Module_context.Flat ->
          [
            `Representations;
            `Definitions;
            `Native_resources;
            `Public_resources;
            `Applications;
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
            `Primitives;
            `Pure_functions;
            `Representations;
            `Definitions;
            `Native_resources;
            `Public_resources;
            `Applications;
            `Fields;
            `State;
            `View_fields;
            `Proof_definitions;
            `Late_members;
            `Predicates;
            `Lemmas;
            `Logical_functions;
            `Procedures;
          ]
    in
    List.concat_map stages ~f:(function
      | `Representations -> representations
      | `Definitions -> emitted_assets destination definition_modules
      | `Native_resources -> native_resources
      | `Public_resources -> emitted_assets destination public_resource_members
      | `Applications -> applications
      | `View_fields -> ghost_fields
      | `Fields -> emitted_fields destination explicit_fields
      | `Proof_definitions -> emitted_assets destination definition_proof_modules
      | `State ->
          state_members group structure_member_lists
          @ state_members group pending_member_lists
          @ state_members group action_check_lists
      | `Late_members -> late_members
      | `Primitives -> primitive_members
      | `Predicates ->
          List.map (emitted_proofs destination predicate_members) ~f:R.Member.callable
      | `Pure_functions ->
          List.map (owned destination pure_funcs) ~f:(fun (_, member) ->
              R.Member.callable member)
      | `Lemmas ->
          List.map (emitted_proofs destination proof_lemma_members) ~f:R.Member.callable
      | `Logical_functions -> emitted_proofs destination logical_members
      | `Procedures -> List.map (owned destination procs) ~f:procedure_member)
  in
  let* generic_implementations =
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
        | None -> Ok worker
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
            let cell_fields =
              List.filter_map !refs ~f:(fun cell ->
                  let name = Qualified_name.of_string cell.cell_name in
                  Option.map
                    (List.Assoc.find field_contexts name.path
                       ~equal:(List.equal String.equal))
                    ~f:(fun substitution ->
                      (name.name, Subst.type_expr substitution cell.cell_type)))
              |> List.dedup_and_sort ~compare:(fun (left, _) (right, _) ->
                  String.compare left right)
            in
            let* cell_fields =
              all cell_fields ~f:(fun (field, elt) ->
                  let* typ =
                    Datatypes.typ cell_environment
                      ~at:group.representative.template.mod_loc elt
                  in
                  Ok (Datatypes.field_member cell_environment ~loc:l field typ elt))
            in
            let shape =
              R.Member.module_ ~loc:l ~interface:true (ident ~loc:l "Shape")
                (data_members @ fields @ cell_fields)
            in
            let factory =
              R.Member.unit_factory ~loc:l
                ~implements:[ (q (world ^ ".Shape"), []) ]
                (ident ~loc:l "Fresh") []
            in
            Ok
              (R.Member.module_ ~loc:l
                 ~params:
                   (List.map (Generic_modules.type_slots group) ~f:(fun stem ->
                        (ident ~loc:l stem, R.Name.make ~loc:l ~path:[ "Library" ] "Type")))
                 (ident ~loc:l world)
                 (List.nth_exn generic_interfaces
                    (List.findi_exn generics ~f:(fun _ candidate ->
                         phys_equal candidate group)
                    |> fst)
                 @ [ shape; factory; worker ])))
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
                            Datatypes.typ concrete ~at:declaration.typ_loc t)
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
  let _, native_blocks =
    List.fold (List.zip_exn checked_modules checked_module_members) ~init:([], [])
      ~f:(fun (emitted, blocks) (view, members) ->
        let binding = view.Checked_modules.binding in
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
        if captured && not final then (emitted, blocks)
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
          let instances =
            List.filter_map generic_instances ~f:(fun (argument, _, instance) ->
                Option.some_if (phys_equal argument binding) instance)
          in
          let publications =
            List.filter_map !publication_members ~f:(fun (owner, member) ->
                Option.some_if
                  (phys_equal owner binding || List.mem attached owner ~equal:phys_equal)
                  (R.Member.callable member))
          in
          let setup =
            List.concat_map generic_instances ~f:(fun (argument, setup, _) ->
                if phys_equal argument binding then setup else [])
          in
          List.iter generics ~f:(fun group ->
              List.iter group.Generic_modules.applications ~f:(fun application ->
                  if
                    phys_equal application.source.argument binding
                    && Option.is_some group.world
                  then available_layouts := application.layout :: !available_layouts));
          let declarations = take_declarations () in
          List.iter generics ~f:(fun group ->
              List.iter group.Generic_modules.applications ~f:(fun application ->
                  if phys_equal application.source.argument binding then
                    available_layouts := application.name :: !available_layouts));
          let after_instances = take_declarations () in
          ( (binding :: attached) @ emitted,
            (prefix @ setup @ declarations @ publications @ attached_members @ members
           @ instances @ after_instances)
            :: blocks ))
  in
  let native_modules = List.concat (List.rev native_blocks) in

  let file_start = { Lexing.dummy_pos with pos_fname = source.file } in
  let start = R.Loc.make file_start file_start in
  let ref_fields =
    List.filter_map !refs ~f:(fun cell ->
        Option.some_if
          (List.is_empty (Qualified_name.of_string cell.cell_name).path)
          cell.cell_declaration)
  in
  let root_members =
    emit_context_members Module_context.Flat ~at:start ~representations:[]
      ~native_resources:deferred_native_resource_members ~applications:native_modules
      ~late_members:(List.concat_map !pending_declarations ~f:snd @ ref_fields)
  in
  Ok
    ( R.Program.make ~loc:start
        (Prelude.members
        @ (if
             shared.dynamic_indices
             || List.exists generic_shared ~f:(fun (_, shared) -> shared.dynamic_indices)
           then Indexed_initialization.members
           else [])
        @ imported_resource_members @ modules @ library_modules @ root_members),
      !origins )
