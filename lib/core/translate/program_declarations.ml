(** The second phase of a program's translation: resources and their layouts, data types,
    declarations and modules, the fields and primitives used, and the predicates. *)

open Base
open Translate_context
open Procedures
open Program_items
open Proof_declarations

type t = {
  source : Source.t;
  all_resources : Source.proof_resource list;
  all_resource_views : Source.proof_resource list;
  private_ra_types : (Generic_proofs.t * Datatypes.t) list;
  proof_assets :
    Proof_scopes.scope option -> Source.proof_resource list * Source.proof_field list;
  layouts : Result_layouts.t list;
  checked_modules : Checked_modules.t list;
  checked_operations : Program_items.checked_operation list;
  pure : Procedures.func list;
  polymorphic_functions : Polymorphic_functions.t list;
  runtime_destinations : Module_context.destination list;
  procedure_signatures : (Base.string * Translate_context.procedure_signature) list;
  atomic_operations : (Source.proof_au * Procedures.func) list;
  token_types : Datatypes.t list;
  generic_models : Datatypes.t list;
  resource_types : Datatypes.t list;
  types : Datatypes.t list;
  native_resource_members : (Base.string * Translate_context.R.Member.t) list;
  imported_resource_members : Translate_context.R.Member.t list;
  public_resource_members : (Source.proof_resource * Translate_context.R.Member.t) list;
  deferred_native_resource_members : Translate_context.R.Member.t list;
  pending_declarations : (Base.string list * Datatypes.R.Member.t list) list;
      (** The declarations not emitted yet, each with the layouts it needs. *)
  modules : Datatypes.R.Member.t list;
  fields : Datatypes.R.Member.t list;
  pending_fields : (Base.string list * Datatypes.R.Member.t list) list;
  functions : Base.string Path_bindings.t;
  lifted : (string * (int * Ident.t list * Ident.t option)) list;
  ocaml_env : Env.t;
  scoped_proofs : Proof_bindings.t;
  scoped_inputs : (string * int) list;
  predicates :
    (Location.t
    * Translate_context.S.predicate
    * Program_items.definition
    * Types.type_expr list)
    list;
  library_preds :
    (Library_modules.t * Caravan_spec.Spec_ast.predicate * Types.type_expr list) list;
  procedures : (Ident.t * string) list;
  generic_procedures : (string * string) list;
}

let asset_worker ~(asset_context : Path.t option -> Module_context.t) owner =
  (asset_context owner).worker

let resource_binding ~(untyped_scoped_proofs : Proof_bindings.t) resource =
  List.find untyped_scoped_proofs.bindings ~f:(fun binding ->
      match binding.Proof_bindings.kind with
      | Resource actual -> Ident.same actual.resource_id resource.Source.resource_id
      | _ -> false)

let resource_view ~(untyped_scoped_proofs : Proof_bindings.t) ~scope resource =
  let resource_binding = resource_binding ~untyped_scoped_proofs in
  match resource_binding resource with
  | Some binding when Proof_bindings.opaque_at untyped_scoped_proofs ~scope binding ->
      Option.value resource.resource_public ~default:resource
  | None ->
      begin match
        List.find untyped_scoped_proofs.applications ~f:(fun view ->
            Path.same
              (Path.Pdot (view.Proof_bindings.path, view.source.entry.name.pid_str))
              resource.Source.resource_path)
      with
      | Some view when Proof_bindings.application_opaque untyped_scoped_proofs ~scope view
        ->
          Option.value resource.resource_public ~default:resource
      | Some _ | None -> resource
      end
  | Some _ -> resource

let is_pure ~(pure : Procedures.func list) (f : func) =
  List.exists pure ~f:(fun g -> Ident.same g.id f.id)

let procedure_stem ~(generic_procedures : (string * string) list) group stem =
  List.Assoc.find_exn generic_procedures
    (group.Generic_modules.name ^ "." ^ stem)
    ~equal:String.equal

let pure_name ~(generics : Generic_modules.t list) f =
  match Generic_modules.member generics f.id with
  | None -> f.raven_name
  | Some (_, application, stem) -> application.name ^ "." ^ stem

let pure_reference ~(generics : Generic_modules.t list) f =
  let pure_name = pure_name ~generics in
  match Generic_modules.member generics f.id with
  | None -> Qualified_name.{ path = []; name = f.raven_name }
  | Some _ -> Qualified_name.of_string (pure_name f)

let proc_name ~(procedures : (Ident.t * string) list) (f : func) =
  List.Assoc.find_exn procedures f.id ~equal:Ident.same

let function_worker polymorphic_functions (f : func) =
  List.find polymorphic_functions ~f:(fun worker ->
      Ident.same worker.Polymorphic_functions.id f.id)

let function_types polymorphic_functions f types =
  match function_worker polymorphic_functions f with
  | None -> types
  | Some worker ->
      List.mapi worker.scheme.variables ~f:(fun index variable ->
          Datatypes.variable_type ~variable
            ~owner:(String.split worker.name ~on:'.')
            ~parameter:("A" ^ Int.to_string index)
            ~at:worker.loc)
      @ types

let worker_member polymorphic_functions f target =
  match function_worker polymorphic_functions f with
  | None -> target
  | Some worker -> worker.name ^ "." ^ (Qualified_name.of_string target).name

let body_proc_name ?(polymorphic_functions = []) ~(generics : Generic_modules.t list)
    ~(generic_procedures : (string * string) list) ~(procedures : (Ident.t * string) list)
    f =
  let procedure_stem = procedure_stem ~generic_procedures in
  let proc_name = proc_name ~procedures in
  worker_member polymorphic_functions f
    (match Generic_modules.member generics f.id with
    | None -> proc_name f
    | Some (group, _, stem) -> group.name ^ "." ^ procedure_stem group stem)

let body_pure_name ?(polymorphic_functions = []) ~(generics : Generic_modules.t list) f =
  let pure_name = pure_name ~generics in
  worker_member polymorphic_functions f
    (match Generic_modules.member generics f.id with
    | None -> pure_name f
    | Some (group, _, stem) -> group.name ^ "." ^ stem)

let body_pure_reference ?(polymorphic_functions = []) ~(generics : Generic_modules.t list)
    f =
  match
    (function_worker polymorphic_functions f, Generic_modules.member generics f.id)
  with
  | None, None -> pure_reference ~generics f
  | _ -> Qualified_name.of_string (body_pure_name ~polymorphic_functions ~generics f)

let body_owner ~(generics : Generic_modules.t list) f =
  match Generic_modules.member generics f.id with
  | None -> None
  | Some (group, application, _) ->
      Some (group, phys_equal application.source group.representative)

let body_module_context ~(module_contexts : Module_context.registry)
    ~(context_for_group : Generic_modules.t -> Module_context.t)
    ~(generics : Generic_modules.t list) f =
  let body_owner = body_owner ~generics in
  match body_owner f with
  | Some (group, _) -> context_for_group group
  | None -> Module_context.for_location module_contexts f.loc

let body_destination ?(polymorphic_functions = []) ~(generics : Generic_modules.t list)
    ~(module_contexts : Module_context.registry)
    ~(context_for_group : Generic_modules.t -> Module_context.t) f =
  let body_owner = body_owner ~generics in
  let body_module_context =
    body_module_context ~module_contexts ~context_for_group ~generics
  in
  let parent =
    match body_owner f with
    | None -> (body_module_context f).destination
    | Some (group, _) -> Module_context.Worker group
  in
  match function_worker polymorphic_functions f with
  | None -> parent
  | Some worker -> Module_context.Function_worker (worker, parent)

let with_body_names ?(polymorphic_functions = []) ~(funcs : Procedures.func list)
    ~(procedures : (Ident.t * string) list) ~(generics : Generic_modules.t list)
    ~(generic_procedures : (string * string) list) entries =
  let proc_name = proc_name ~procedures in
  let body_proc_name =
    body_proc_name ~polymorphic_functions ~generics ~generic_procedures ~procedures
  in
  let body_owner = body_owner ~generics in
  entries
  @ List.filter_map funcs ~f:(fun f ->
      match body_owner f with
      | (Some (_, true) | None) when not (String.equal (proc_name f) (body_proc_name f))
        ->
          Option.map
            (List.Assoc.find entries (proc_name f) ~equal:String.equal)
            ~f:(fun value -> (body_proc_name f, value))
      | Some _ | None -> None)

let au_plan ~(asset_context : Path.t option -> Module_context.t) (au : Source.proof_au) =
  let asset_worker = asset_worker ~asset_context in
  if Option.is_none au.au_application then asset_worker au.au_scope else None

let au_procedure ~(procedures : (Ident.t * string) list)
    ~(generics : Generic_modules.t list) ~(generic_procedures : (string * string) list)
    ~(asset_context : Path.t option -> Module_context.t) au f =
  let proc_name = proc_name ~procedures in
  let body_proc_name = body_proc_name ~generics ~generic_procedures ~procedures in
  let au_plan = au_plan ~asset_context in
  match au_plan au with Some _ -> body_proc_name f | None -> proc_name f

let au_application_view ~(untyped_scoped_proofs : Proof_bindings.t) (au : Source.proof_au)
    =
  Option.bind au.au_application ~f:(fun (_, template) ->
      List.find untyped_scoped_proofs.applications ~f:(fun view ->
          match view.source.kind with
          | Atomic original ->
              Ident.same original.au_id template
              && Path.same au.au_path (Path.Pdot (view.path, au.au_name))
          | _ -> false))

(** The declarations of [pending] whose layouts are all [available], with those still
    pending. *)
let take_declarations ~available pending =
  let ready, pending =
    List.partition_tf pending ~f:(fun (dependencies, _) ->
        List.for_all dependencies ~f:(fun name ->
            List.mem available name ~equal:String.equal))
  in
  (List.concat_map ready ~f:snd, pending)

let run (scopes : Program_scopes.t) : (t, error) Result.t =
  let {
    Program_scopes.funcs;
    generic_proof_types;
    generic_proofs;
    generics;
    implementation;
    inventory;
    libraries;
    module_contexts;
    scoped_proofs = untyped_scoped_proofs;
    source = unprojected_source;
    types = source_types;
    _;
  } =
    scopes
  in
  let asset_context =
    Program_scopes.asset_context ~module_contexts:scopes.module_contexts
  in
  let source =
    let project_descriptor context backend abstract_member descriptor =
      if List.is_empty context.Module_context.namespace then descriptor
      else
        let descriptor =
          List.fold (Option.value_map abstract_member ~default:[] ~f:fst) ~init:descriptor
            ~f:(fun descriptor parameter ->
              match abstract_member with
              | Some (_, member) ->
                  Datatypes.with_paths descriptor
                    [ Path.Pdot (Path.Pdot (Path.Pident parameter, member), "t") ]
              | None -> descriptor)
        in
        {
          descriptor with
          Datatypes.module_name = backend;
          module_path = Some (String.split backend ~on:'.');
          backend_type =
            Some Qualified_name.{ path = String.split backend ~on:'.'; name = "T" };
        }
    in
    {
      unprojected_source with
      proof_resources =
        List.map unprojected_source.proof_resources ~f:(fun resource ->
            let context = asset_context resource.Source.resource_scope in
            let parameter =
              if resource.resource_abstract then
                List.find context.parameters ~f:(fun parameter ->
                    Option.exists parameter.Generic_proofs.original ~f:(fun original ->
                        Source.resource_has_path resource
                          (Path.Pdot (Path.Pident original, resource.resource_name))))
              else None
            in
            let backend =
              Module_context.member context
                (Option.value_map parameter ~default:resource.resource_backend
                   ~f:(fun parameter ->
                     parameter.generic.parameter ^ "." ^ resource.resource_name))
            in
            let abstract_member =
              Option.map parameter ~f:(fun parameter ->
                  ( Option.to_list parameter.original @ [ parameter.instance.parameter ],
                    resource.resource_name ))
            in
            {
              resource with
              resource_backend = backend;
              resource_descriptor =
                project_descriptor context backend abstract_member
                  resource.resource_descriptor;
              resource_aliases =
                List.map resource.resource_aliases
                  ~f:(project_descriptor context backend None);
              resource_public =
                Option.map resource.resource_public ~f:(fun public ->
                    let backend = Module_context.member context public.resource_backend in
                    {
                      public with
                      resource_backend = backend;
                      resource_descriptor =
                        project_descriptor context backend None public.resource_descriptor;
                    });
            });
      proof_fields =
        List.map unprojected_source.proof_fields ~f:(fun field ->
            let context = asset_context field.Source.field_scope in
            {
              field with
              field_backend = Module_context.member context field.field_backend;
            });
    }
  in
  let resource_views resource =
    resource :: Option.to_list resource.Source.resource_public
  in
  let application_resources =
    Generic_proofs.resource_applications source inventory generic_proofs
    |> List.map ~f:(fun resource ->
        match
          List.find source.proof_resources ~f:(fun view ->
              Option.is_some view.Source.resource_application
              && Path.same view.resource_path resource.Source.resource_path)
        with
        | None -> resource
        | Some view ->
            {
              resource with
              resource_id = view.resource_id;
              resource_application = view.resource_application;
              resource_public =
                Option.map resource.resource_public ~f:(fun public ->
                    Option.value_map view.resource_public ~default:public ~f:(fun view ->
                        { public with resource_id = view.resource_id }));
            })
  in
  let all_resources =
    application_resources
    @ List.filter source.proof_resources ~f:(fun r ->
        Option.is_none r.Source.resource_application)
  in
  let all_resource_views = List.concat_map all_resources ~f:resource_views in
  let resource_view = resource_view ~untyped_scoped_proofs in
  let private_ra_types =
    List.filter_map source.proof_types ~f:(fun data ->
        Option.bind (Generic_proofs.model_owner source data) ~f:(fun scope ->
            if Option.is_none scope.Proof_scopes.definition then None
            else
              Option.map (Generic_proofs.owner generic_proofs (Some scope))
                ~f:(fun plan ->
                  let backend = plan.group.name ^ "." ^ data.Datatypes.module_name in
                  ( plan,
                    {
                      data with
                      module_path = Some (String.split backend ~on:'.');
                      backend_type =
                        Some
                          Qualified_name.
                            { path = String.split backend ~on:'.'; name = "T" };
                    } ))))
  in
  let proof_assets scope =
    let environment =
      Option.value_map scope ~default:source.env ~f:(fun scope ->
          Source.annotation_env source scope.Proof_scopes.environment)
    in
    let rebase = Proof_bindings.context_type untyped_scoped_proofs ~environment in
    let private_owner owner =
      match (owner, scope) with
      | None, _ -> true
      | Some owner, Some caller ->
          Option.exists (Proof_scopes.find_owner source.proof_scopes (Some owner))
            ~f:(fun owner ->
              Option.is_some
                (Proof_bindings.drop_prefix owner.namespace caller.Proof_scopes.namespace))
      | Some _, None -> false
    in
    let project owner typ =
      if private_owner owner then typ
      else rebase (Proof_bindings.public_type untyped_scoped_proofs typ)
    in
    let visible entry =
      Option.value_map entry ~default:true
        ~f:(Proof_bindings.visible untyped_scoped_proofs ~scope)
    in
    let resources =
      List.filter_map
        (List.filter source.proof_resources ~f:(fun resource ->
             Option.is_none resource.Source.resource_application))
        ~f:(fun resource ->
          let binding =
            List.find untyped_scoped_proofs.bindings ~f:(fun binding ->
                match binding.kind with
                | Resource actual ->
                    Ident.same actual.resource_id resource.Source.resource_id
                | _ -> false)
          in
          if not (visible binding) then None
          else
            let resource = resource_view ~scope resource in
            let project = project resource.resource_scope in
            Some
              {
                resource with
                resource_type = project resource.resource_type;
                resource_operations =
                  List.map resource.resource_operations ~f:(fun (name, inputs, output) ->
                      (name, List.map inputs ~f:project, project output));
              })
    in
    let fields =
      List.filter_map source.proof_fields ~f:(fun field ->
          let binding =
            List.find untyped_scoped_proofs.bindings ~f:(fun binding ->
                match binding.kind with
                | Field actual -> Ident.same actual.field_id field.Source.field_id
                | _ -> false)
          in
          if not (visible binding) then None
          else
            let project = project field.field_scope in
            Some
              {
                field with
                field_owner = project field.field_owner;
                field_value = project field.field_value;
              })
    in
    let application_resources =
      List.filter_map application_resources ~f:(fun resource ->
          let view =
            List.find untyped_scoped_proofs.applications ~f:(fun view ->
                Path.same
                  (Path.Pdot (view.Proof_bindings.path, view.source.entry.name.pid_str))
                  resource.Source.resource_path)
          in
          match view with
          | Some view
            when Proof_bindings.application_visible untyped_scoped_proofs ~scope view ->
              Some
                (if Proof_bindings.application_opaque untyped_scoped_proofs ~scope view
                 then Option.value resource.resource_public ~default:resource
                 else resource)
          | Some _ | None -> None)
    in
    let application_fields =
      List.filter_map untyped_scoped_proofs.applications ~f:(fun view ->
          match view.Proof_bindings.source.kind with
          | Field original
            when Proof_bindings.application_visible untyped_scoped_proofs ~scope view ->
              Option.map
                (List.find source.proof_fields ~f:(fun field ->
                     Ident.same field.Source.field_id original.field_id))
                ~f:(fun field ->
                  let prefix = (Qualified_name.of_string view.backend).path in
                  let leaf = (Qualified_name.of_string field.field_backend).name in
                  {
                    field with
                    field_path = Path.Pdot (view.path, field.field_name);
                    field_backend = String.concat ~sep:"." (prefix @ [ leaf ]);
                    field_owner = view.project_type field.field_owner;
                    field_value = view.project_type field.field_value;
                    field_resource =
                      Option.map field.field_resource ~f:(fun owner ->
                          match
                            Types.get_desc
                              (view.project_type
                                 (Ctype.newconstr (Path.Pdot (owner, "t")) []))
                          with
                          | Tconstr (Path.Pdot (owner, "t"), [], _) -> owner
                          | _ -> owner);
                  })
          | _ -> None)
    in
    (resources @ application_resources, fields @ application_fields)
  in
  let layouts = Result_layouts.plan source_types generics in
  let* types = Result_layouts.concrete layouts source_types in
  let schema binding =
    Option.map (Generic_modules.application_for_binding generics binding)
      ~f:(fun (group, application) ->
        Checked_modules.
          {
            interface = Generic_modules.interface group application;
            members = group.operations;
          })
  in
  let checked_modules = Checked_modules.plan ~schema inventory.bindings in
  let* checked_operations =
    all checked_modules ~f:(fun view ->
        let binding = view.Checked_modules.binding in
        all binding.Module_inventory.expected.signature_values
          ~f:(fun (member, signature) ->
            let* contract = signature_contract signature in
            let* () =
              match contract with
              | Some c when c.S.pure || Option.is_some c.continues ->
                  unsupported signature.site.item_loc
                    "A pure or continuation contract in a checked module view"
              | _ -> Ok ()
            in
            let operation_member =
              List.Assoc.find_exn view.members member ~equal:String.equal
            in
            Ok
              {
                operation_binding = binding;
                operation_signature = signature;
                operation_contract = contract;
                operation_name =
                  (if view.grouped then view.name ^ "." ^ operation_member
                   else operation_member);
                operation_member;
                operation_paths =
                  List.map binding.paths ~f:(fun path -> Path.Pdot (path, member));
              }))
  in
  let checked_operations = List.concat checked_operations in

  (* The data types, and the sequences of specifications, which have no module. *)
  let* inferred_pure = pure_functions funcs in
  let pure =
    inferred_pure
    @ List.filter funcs ~f:(fun f ->
        let inferred id =
          List.exists inferred_pure ~f:(fun pure -> Ident.same pure.id id)
        in
        (not (inferred f.id))
        && Option.exists (Generic_modules.member generics f.id)
             ~f:(fun (group, _, stem) ->
               List.exists group.applications ~f:(fun application ->
                   List.exists application.source.body_members ~f:(fun (source, id) ->
                       String.equal
                         (List.Assoc.find_exn group.body_members source
                            ~equal:String.equal)
                         stem
                       && inferred id))))
  in
  let is_pure = is_pure ~pure in
  let generic_procedures =
    List.concat_map generics ~f:(fun group ->
        List.map group.body_members ~f:(fun (source, stem) ->
            let id =
              List.Assoc.find_exn group.representative.body_members source
                ~equal:String.equal
            in
            let f = List.find_exn funcs ~f:(fun f -> Ident.same f.id id) in
            ( group.name ^ "." ^ stem,
              if is_pure f then Fresh_names.fresh (stem ^ "_impl") else stem )))
  in
  let procedure_stem = procedure_stem ~generic_procedures in
  let procedures =
    List.map funcs ~f:(fun f ->
        let name =
          match Generic_modules.member generics f.id with
          | None ->
              if is_pure f then Fresh_names.fresh (f.raven_name ^ "_impl")
              else f.raven_name
          | Some (group, application, stem) ->
              application.name ^ "." ^ procedure_stem group stem
        in
        (f.id, name))
  in
  let proc_name = proc_name ~procedures in
  let* polymorphic_functions =
    all funcs ~f:(fun f ->
        let representative =
          match body_owner ~generics f with
          | Some (_, false) -> false
          | Some (_, true) | None -> true
        in
        let* scheme = Polymorphic_functions.discover ~at:f.loc f.scheme_type in
        if (not representative) || List.is_empty scheme.variables then Ok None
        else
          let source_binding =
            List.exists inventory.values ~f:(fun entry ->
                match entry.Module_inventory.binding.vb_pat.pat_desc with
                | Tpat_var (id, _, _) -> Ident.same id f.id
                | _ -> false)
          in
          let* () =
            if source_binding then Ok ()
            else unsupported f.loc "Generalized local functions"
          in
          let context =
            body_module_context ~module_contexts
              ~context_for_group:(Program_scopes.context_for_group ~module_contexts)
              ~generics f
          in
          let name =
            String.concat ~sep:"."
              (context.namespace @ [ Fresh_names.fresh ("Poly$" ^ f.raven_name) ])
          in
          Ok
            (Some
               Polymorphic_functions.
                 { id = f.id; paths = f.paths; scheme; name; loc = f.loc }))
    |> Result.map ~f:List.filter_opt
  in
  let* () =
    List.fold_result funcs ~init:() ~f:(fun () f ->
        let enclosing =
          List.find polymorphic_functions ~f:(fun worker ->
              (not (Ident.same worker.id f.id))
              && Proof_bindings.contains worker.loc f.loc
              && not
                   (List.exists inventory.values ~f:(fun entry ->
                        match entry.Module_inventory.binding.vb_pat.pat_desc with
                        | Tpat_var (id, _, _) -> Ident.same id f.id
                        | _ -> false)))
        in
        match enclosing with
        | None -> Ok ()
        | Some _ -> unsupported f.loc "Local functions within polymorphic functions")
  in
  let* () =
    List.fold_result funcs ~init:() ~f:(fun () f ->
        match function_worker polymorphic_functions f with
        | None -> Ok ()
        | Some _ ->
            let references = Program_items.referenced f.body in
            if
              List.exists polymorphic_functions ~f:(fun other ->
                  (not (Ident.same other.id f.id))
                  && other.loc.loc_start.pos_cnum >= f.loc.loc_start.pos_cnum
                  && List.mem references other.id ~equal:Ident.same)
            then unsupported f.loc "Mutually recursive polymorphic functions"
            else Ok ())
  in
  let runtime_destinations =
    Module_context.Flat
    :: List.map generics ~f:(fun group -> Module_context.Worker group)
    @ List.filter_map funcs ~f:(fun f ->
        Option.map (function_worker polymorphic_functions f) ~f:(fun _ ->
            body_destination ~polymorphic_functions ~generics ~module_contexts
              ~context_for_group:(Program_scopes.context_for_group ~module_contexts)
              f))
  in
  let with_body_names lifted_argument =
    with_body_names ~polymorphic_functions ~funcs ~procedures ~generics
      ~generic_procedures lifted_argument
  in
  let* procedure_signatures =
    all funcs ~f:(fun f ->
        let outputs = ghost_results f in
        let* () =
          match outputs with
          | (id, _) :: _ when is_pure f ->
              unsupported id.pid_loc "Ghost results of a pure function"
          | (id, _) :: _ when not f.manual ->
              unsupported id.pid_loc "Ghost results require a manual function proof"
          | _ -> Ok ()
        in
        let declared xs =
          all xs ~f:(fun (id, pty) ->
              let* t = Source.ocaml_type f.environment ~at:id.S.pid_loc pty in
              Ok (id.pid_str, t))
        in
        let* procedure_inputs = declared (ghost_params f) in
        let* procedure_outputs = declared outputs in
        Ok
          ( proc_name f,
            { procedure_inputs; procedure_outputs; procedure_result = f.body.exp_type } ))
  in
  let procedure_signatures = with_body_names procedure_signatures in
  let au_plan = au_plan ~asset_context in
  let au_procedure =
    au_procedure ~procedures ~generics ~generic_procedures ~asset_context
  in
  let applied_atomic_operation (au : Source.proof_au) =
    let ( let* ) value f = Option.bind value ~f in
    let* identity, template = au.au_application in
    let* binding =
      List.find untyped_scoped_proofs.bindings ~f:(fun binding ->
          match binding.Proof_bindings.kind with
          | Atomic original -> Ident.same original.au_id template
          | _ -> false)
    in
    let* plan = Generic_proofs.owner generic_proofs (Some binding.entry.scope) in
    let* operation =
      match binding.kind with
      | Atomic original -> Some original.au_operation_path
      | _ -> None
    in
    let* application =
      List.find plan.group.applications ~f:(fun application ->
          Path.same application.source.identity identity)
    in
    let* id = Generic_proofs.function_id plan ~instance:application.source operation in
    List.find funcs ~f:(fun f -> Ident.same f.id id)
  in
  let* atomic_operations =
    all source.proof_aus ~f:(fun (au : Source.proof_au) ->
        let operation =
          match au_plan au with
          | None ->
              Option.first_some
                (List.find funcs ~f:(fun f ->
                     List.mem f.paths au.au_operation_path ~equal:Path.same))
                (applied_atomic_operation au)
          | Some plan ->
              Option.bind (Generic_proofs.function_id plan au.au_operation_path)
                ~f:(fun id -> List.find funcs ~f:(fun f -> Ident.same f.id id))
        in
        match operation with
        | None ->
            error au.au_at "An AU facade must name a procedure in this implementation"
        | Some f when not (Option.exists f.contract ~f:(fun c -> c.atomic)) ->
            error au.au_at "An AU facade requires a logically atomic contract"
        | Some f -> Ok (au, f))
  in
  let token_types =
    List.map atomic_operations ~f:(fun (au, f) ->
        Datatypes.with_paths
          (Datatypes.atomic_token ~path:au.Source.au_token_path
             ~procedure:(au_procedure au f) ~at:au.au_at)
          au.au_token_paths)
  in
  let generic_models = Generic_proofs.model_types source inventory generic_proofs in
  let generic_model data =
    List.exists generic_proofs ~f:(fun plan ->
        List.exists (Generic_proofs.models source plan) ~f:(fun model ->
            Poly.equal model.Datatypes.at data.Datatypes.at))
  in
  let private_ra_type data =
    List.exists private_ra_types ~f:(fun (_, owned) ->
        Poly.equal data.Datatypes.at owned.Datatypes.at)
  in
  let data_types =
    List.filter types ~f:(fun data ->
        (not (generic_model data)) && not (private_ra_type data))
  in
  let resource_types =
    List.concat_map all_resource_views ~f:(fun r ->
        r.Source.resource_descriptor :: r.resource_aliases)
  in
  let* generic_runtime_types =
    all generic_proofs ~f:(fun plan ->
        let* layouts =
          Result_layouts.symbolic layouts plan.Generic_proofs.group
            ~owner:(String.split plan.group.name ~on:'.' @ [ "Layout" ])
        in
        Ok
          (List.filter_map (Generic_proofs.runtime_types plan) ~f:(fun declaration ->
               Option.map
                 (List.find layouts ~f:(fun descriptor ->
                      Option.exists descriptor.Datatypes.id ~f:(fun id ->
                          String.equal (Ident.name id) declaration.Typedtree.typ_name.txt)
                      && Poly.equal descriptor.at declaration.typ_loc))
                 ~f:(fun descriptor ->
                   {
                     descriptor with
                     id = Some declaration.typ_id;
                     paths = [];
                     library = None;
                   }))))
    |> Result.map ~f:List.concat
  in
  let types =
    generic_runtime_types
    @ List.map private_ra_types ~f:snd
    @ generic_models @ generic_proof_types @ types @ resource_types @ token_types
    @ source.logical_types
    @ match source.sequence with Pident id -> [ Datatypes.sequence id ] | _ -> []
  in
  (* Each data type's module, given the ones declared before it; a record type that is a
     reference has fields instead. *)
  let* modules =
    all
      (List.filter_mapi data_types ~f:(fun i (d : Datatypes.t) ->
           Option.some_if
             (Option.is_none d.heap && Option.is_none d.alias
             && not (Result_layouts.contains layouts d))
             (List.take data_types i, d)))
      ~f:(fun (before, d) ->
        let* member =
          Datatypes.member
            (generic_proof_types @ generic_models @ before @ resource_types @ token_types
           @ source.logical_types)
            d
        in
        Ok (d.Datatypes.module_name, member))
  in
  let proof_module path ~at =
    match
      List.find all_resources ~f:(fun resource -> Source.resource_has_path resource path)
    with
    | Some resource -> Ok resource
    | None -> error at "The proof module argument has no translated declaration"
  in
  let rec depends_on_definition seen resource =
    if Option.is_some resource.Source.resource_application then false
    else if List.mem seen resource.resource_id ~equal:Ident.same then false
    else if resource.resource_definition then true
    else
      let seen = resource.resource_id :: seen in
      let dependency path =
        List.exists source.proof_resources ~f:(fun argument ->
            (Path.same path argument.resource_path
            || Path.same path (Path.Pident argument.resource_id))
            && depends_on_definition seen argument)
      in
      Option.exists resource.resource_alias_of ~f:dependency
      || List.exists resource.resource_arguments ~f:(function
        | Source.Type_argument _ -> false
        | Module_argument path -> dependency path)
  in
  let deferred_resources =
    List.filter source.proof_resources ~f:(fun resource ->
        Option.is_none resource.Source.resource_application
        && Module_context.emits_owner module_contexts ~destination:Module_context.Flat
             resource.resource_scope
        && depends_on_definition [] resource)
  in
  let* native_resource_members =
    all
      (List.filter source.proof_resources ~f:(fun resource ->
           (not resource.Source.resource_abstract)
           && Option.is_none resource.resource_application))
      ~f:(fun resource ->
        let at = resource.Source.resource_at in
        let l = loc at in
        let* member =
          match (resource.resource_definition, resource.resource_alias_of) with
          | true, _ ->
              let* backend =
                match implementation resource with
                | Some backend -> Ok backend
                | None -> error at "Missing resource algebra implementation"
              in
              let interface =
                qualified_name ~loc:l (String.concat ~sep:"." resource.resource_functor)
              in
              Ok
                (R.Member.alias ~loc:l ~typ:interface ~sealed:true
                   (ident ~loc:l (Qualified_name.of_string resource.resource_backend).name)
                   (qualified_name ~loc:l backend))
          | false, Some path ->
              let* target = proof_module path ~at in
              Ok
                (R.Member.alias ~loc:l
                   (ident ~loc:l (Qualified_name.of_string resource.resource_backend).name)
                   (qualified_name ~loc:l target.resource_backend))
          | false, None ->
              let* arguments =
                all resource.resource_arguments ~f:(function
                  | Source.Type_argument typ -> Datatypes.typ types ~at typ
                  | Module_argument path ->
                      let* argument = proof_module path ~at in
                      Ok
                        (R.Type.named ~loc:l
                           (qualified_name ~loc:l argument.resource_backend)
                           []))
              in
              let library =
                qualified_name ~loc:l (String.concat ~sep:"." resource.resource_functor)
              in
              Ok
                (R.Member.instance ~loc:l ~def:(library, arguments)
                   (ident ~loc:l (Qualified_name.of_string resource.resource_backend).name)
                   library)
        in
        Ok (resource.resource_backend, member))
  in
  let imported_resource_members =
    List.filter_map source.proof_resources ~f:(fun resource ->
        if
          resource.Source.resource_abstract
          && Option.is_none resource.resource_scope
          && Option.is_none resource.resource_application
        then
          let l = loc resource.resource_at in
          Some
            (R.Member.free
               (R.Member.instance ~loc:l
                  (ident ~loc:l resource.resource_backend)
                  (qualified_name ~loc:l
                     (String.concat ~sep:"." resource.resource_functor))))
        else None)
  in
  let public_resource_members =
    List.filter_map
      (List.filter source.proof_resources ~f:(fun resource ->
           Option.is_none resource.Source.resource_application))
      ~f:(fun resource ->
        Option.map resource.Source.resource_public ~f:(fun public ->
            let l = loc public.resource_at in
            ( resource,
              R.Member.alias ~loc:l
                ~typ:
                  (qualified_name ~loc:l (String.concat ~sep:"." public.resource_functor))
                (ident ~loc:l (Qualified_name.of_string public.resource_backend).name)
                (qualified_name ~loc:l resource.resource_backend) )))
  in
  let proof_module_names =
    List.map source.proof_types ~f:(fun data -> data.Datatypes.module_name)
  in
  let runtime_modules =
    List.filter_map modules ~f:(fun (name, member) ->
        Option.some_if (not (List.mem proof_module_names name ~equal:String.equal)) member)
  in
  let proof_modules =
    List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
        match entry.Proof_scopes.declaration with
        | S.Proof_type _ ->
            Option.bind
              (List.find source.proof_types ~f:(fun data ->
                   Poly.equal data.Datatypes.at entry.name.pid_loc))
              ~f:(fun data ->
                List.Assoc.find modules data.module_name ~equal:String.equal)
        | Proof_resource _ ->
            Option.bind
              (List.find source.proof_resources ~f:(fun resource ->
                   Poly.equal resource.Source.resource_at entry.name.pid_loc
                   && Module_context.emits_owner module_contexts
                        ~destination:Module_context.Flat resource.resource_scope
                   && not (depends_on_definition [] resource)))
              ~f:(fun resource ->
                List.Assoc.find native_resource_members resource.resource_backend
                  ~equal:String.equal)
        | _ -> None)
  in
  let deferred_native_resource_members =
    List.filter_map deferred_resources ~f:(fun resource ->
        List.Assoc.find native_resource_members resource.resource_backend
          ~equal:String.equal)
  in
  let rec resource_dependencies seen resource =
    let application =
      List.find_map generics ~f:(fun group ->
          List.find_map group.Generic_modules.applications ~f:(fun application ->
              Option.some_if
                (List.is_prefix
                   (String.split resource.Source.resource_backend ~on:'.')
                   ~prefix:[ application.name ] ~equal:String.equal)
                application.name))
    in
    if Option.is_some application then Ok (Option.to_list application)
    else if List.mem seen resource.Source.resource_id ~equal:Ident.same then Ok []
    else
      let* aliases =
        match resource.resource_alias_of with
        | None -> Ok []
        | Some path ->
            let* target = proof_module path ~at:resource.resource_at in
            resource_dependencies (resource.resource_id :: seen) target
      in
      let* dependencies =
        all resource.resource_arguments ~f:(function
          | Source.Type_argument typ ->
              Ok
                (Result_layouts.type_dependencies
                   ~additional:(Generic_proofs.layout_dependencies generic_proofs)
                   layouts types typ)
          | Module_argument path ->
              let* argument = proof_module path ~at:resource.resource_at in
              resource_dependencies (resource.resource_id :: seen) argument)
      in
      Ok (aliases @ List.concat dependencies)
  in
  let* module_declarations =
    all (runtime_modules @ proof_modules) ~f:(fun member ->
        let* dependencies =
          match
            List.find modules ~f:(fun (_, candidate) -> phys_equal member candidate)
          with
          | Some (source_name, _) ->
              let data =
                List.find_exn data_types ~f:(fun d ->
                    String.equal d.Datatypes.module_name source_name)
              in
              Ok
                (Result_layouts.dependencies
                   ~additional:(Generic_proofs.layout_dependencies generic_proofs)
                   layouts types data)
          | None ->
              let resource_name =
                fst
                  (List.find_exn native_resource_members ~f:(fun (_, candidate) ->
                       phys_equal member candidate))
              in
              let resource =
                List.find_exn source.proof_resources ~f:(fun r ->
                    String.equal r.Source.resource_backend resource_name)
              in
              resource_dependencies [] resource
        in
        Ok (dependencies, [ member ]))
  in
  let* field_declarations =
    all
      (List.filter types ~f:(fun d ->
           (not (Result_layouts.contains layouts d))
           && not (List.mem generic_runtime_types d ~equal:phys_equal)))
      ~f:(fun d ->
        let* fields = Datatypes.fields ~declarations:[ d ] types in
        Ok
          ( Result_layouts.dependencies
              ~additional:(Generic_proofs.layout_dependencies generic_proofs)
              layouts types d,
            fields ))
  in
  let modules, pending_declarations =
    take_declarations ~available:[] module_declarations
  in
  let fields, pending_fields = take_declarations ~available:[] field_declarations in
  let functions =
    Path_bindings.of_list
      (List.concat_map funcs ~f:(fun f ->
           List.map f.paths ~f:(fun path -> (path, proc_name f)))
      @ List.concat_map checked_operations ~f:(fun operation ->
          List.map operation.operation_paths ~f:(fun path ->
              (path, operation.operation_name))))
  in
  let lifted =
    List.filter_map funcs ~f:(fun f ->
        Option.some_if
          ((not (List.is_empty f.prefix))
          || (not (List.is_empty f.captured))
          || Option.is_some f.role)
          (proc_name f, (f.prefix_count, f.captured, f.role)))
  in
  let lifted = with_body_names lifted in
  let ocaml_env = source.env in
  (* The predicates' signatures first, for their bodies and the contracts to use. *)
  let* predicates = predicates source in
  let* () = check_scoped_resources ~types source inventory untyped_scoped_proofs in
  let* applications =
    all untyped_scoped_proofs.applications ~f:(fun view ->
        let formal =
          List.find_map (List.rev view.constraints) ~f:(fun constraint_ ->
              List.Assoc.find constraint_.Module_inventory.signature.signature_resources
                view.source.entry.name.pid_str ~equal:String.equal
              |> Option.map ~f:(fun formal -> (constraint_, formal)))
        in
        match (formal, view.source.kind) with
        | Some (constraint_, formal), Predicate _ ->
            let environment =
              Source.annotation_env source formal.Module_inventory.site.environment
            in
            let* raw =
              Proof_bindings.parameter_types environment formal.declaration.pred_params
            in
            let projection =
              Proof_bindings.signature_type_projection Subst.identity view.path
                constraint_.signature
            in
            Ok { view with types = List.map raw ~f:(Subst.type_expr projection) }
        | _ -> Ok view)
  in
  let scoped_proofs =
    Proof_bindings.with_applications untyped_scoped_proofs applications
  in
  let* scoped_predicates =
    all (List.filter_map scoped_proofs.bindings ~f:scoped_predicate)
      ~f:(fun ((_, p, _, ts) as declaration) ->
        let* _ = implicit_parameters p in
        Ok declaration)
  in
  let* scoped_inputs =
    all scoped_predicates ~f:(fun (_, p, _, ts) ->
        let* implicit = implicit_parameters p in
        Ok (p.pred_name.pid_str, List.length ts - implicit))
  in
  let predicates = predicates @ scoped_predicates in
  (* The abstract predicates of the libraries, by their qualified names, as [Cell.holds],
     whose parameters' types are the library's own where it declares them. *)
  let* library_preds =
    all libraries ~f:(fun (lib : Library_modules.t) ->
        let* environment = Library_modules.environment source lib in
        all
          (List.filter
             (Annotation.of_comments lib.library.interface_comments)
             ~f:(Annotation.predicate_declaration ~interface:true))
          ~f:(fun a ->
            let* p = Annotation.predicate a in
            let* () =
              match p.pred_body with
              | Some _ -> unsupported a.loc "A predicate of a library with a definition"
              | None -> Ok ()
            in
            let* types =
              all p.pred_params ~f:(fun (_, t) ->
                  Source.ocaml_type environment ~at:a.loc t)
            in
            Ok (lib, p, types)))
  in
  let library_preds = List.concat library_preds in
  Ok
    {
      source;
      all_resources;
      all_resource_views;
      private_ra_types;
      proof_assets;
      layouts;
      checked_modules;
      checked_operations;
      pure;
      polymorphic_functions;
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
      modules;
      fields;
      pending_fields;
      functions;
      lifted;
      ocaml_env;
      scoped_proofs;
      scoped_inputs;
      predicates;
      library_preds;
      procedures;
      generic_procedures;
    }
