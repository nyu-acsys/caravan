(** Symbolic proof ownership in generic workers. *)

open Base

let ( let* ) = Result.( >>= )

type t = {
  group : Generic_modules.t;
  scope : Proof_scopes.scope;
  parameter : Ident.t;
  aliases : (Typedtree.type_declaration * Typedtree.type_declaration) list;
}

let model_owner (source : Source.t) (data : Datatypes.t) =
  List.find_map source.proof_scopes.declarations ~f:(fun entry ->
      match entry.Proof_scopes.declaration with
      | Proof_type _ when Poly.equal entry.name.pid_loc data.at -> Some entry.scope
      | _ -> None)

let models source plan =
  List.filter source.Source.proof_types ~f:(fun data ->
      Option.exists (model_owner source data) ~f:(fun scope ->
          Option.equal Path.same scope.owner plan.scope.owner))

let resources source plan =
  List.filter source.Source.proof_resources ~f:(fun resource ->
      (not resource.Source.resource_abstract)
      && Option.equal Path.same resource.resource_scope plan.scope.owner)

let has_models source (specialization : Module_inventory.specialization) =
  match specialization.template.mod_desc with
  | Tmod_functor (Named (Some parameter, _, _), _) ->
      List.exists source.Source.proof_types ~f:(fun data ->
          Option.exists (model_owner source data) ~f:(fun scope ->
              match scope.parameters with
              | [ Named (Some id, _, _) ] -> Ident.same id parameter
              | _ -> false))
  | _ -> false

let model_descriptor data ~owner =
  let path = owner @ [ data.Datatypes.module_name ] in
  {
    data with
    module_path = Some path;
    backend_type = Some Qualified_name.{ path; name = "T" };
  }

let symbolic_models source plan ~owner =
  List.map (models source plan) ~f:(fun data -> model_descriptor data ~owner)

let parameter_types plan ~owner =
  let descriptors = Generic_modules.types plan.group ~owner in
  let formal_types, ghost_types =
    List.split_n descriptors (List.length plan.group.types)
  in
  let formal_types =
    List.map2_exn plan.group.types formal_types ~f:(fun (name, _) descriptor ->
        let path = Path.Pdot (Path.Pident plan.parameter, name) in
        { descriptor with Datatypes.id = None; library = Some path; paths = [ path ] })
  in
  let ghost_types =
    List.map2_exn plan.group.representative.argument.expected.signature_ghost_modules
      ghost_types ~f:(fun (name, _) descriptor ->
        Datatypes.with_paths descriptor
          [ Path.Pdot (Path.Pdot (Path.Pident plan.parameter, name), "t") ])
  in
  formal_types @ ghost_types

let model_projection source plan path substitution =
  List.fold (models source plan) ~init:substitution ~f:(fun substitution data ->
      Option.value_map data.Datatypes.id ~default:substitution ~f:(fun id ->
          Subst.add_type id (Path.Pdot (path, Ident.name id)) substitution))

let resource_projection source plan path substitution =
  let substitution =
    match plan.scope.owner with
    | Some (Path.Pident id) -> Subst.add_module id path substitution
    | Some (Pdot _ | Papply _ | Pextra_ty _) | None -> substitution
  in
  List.fold (resources source plan) ~init:substitution ~f:(fun substitution resource ->
      let owner = Path.Pdot (path, resource.resource_name) in
      let add_resource substitution resource =
        let substitution =
          Subst.add_module resource.Source.resource_id owner substitution
        in
        List.fold resource.resource_type_members ~init:substitution
          ~f:(fun substitution (member, id, _) ->
            Subst.add_type id (Path.Pdot (owner, String.uncapitalize member)) substitution)
      in
      let substitution = add_resource substitution resource in
      Option.value_map resource.resource_public ~default:substitution
        ~f:(add_resource substitution))

let nullary_alias (declaration : Typedtree.type_declaration) =
  match declaration.typ_kind with
  | Ttype_abstract ->
      List.is_empty declaration.typ_params && Option.is_some declaration.typ_manifest
  | _ -> false

let plan groups scopes =
  let candidates =
    List.filter_map scopes.Proof_scopes.scopes ~f:(fun scope ->
        match scope.parameters with
        | [ Named (Some parameter, _, _) ] ->
            Option.map
              (List.find groups ~f:(fun group ->
                   match group.Generic_modules.representative.template.mod_desc with
                   | Tmod_functor (Named (Some source, _, _), _) ->
                       Ident.same source parameter
                   | _ -> false))
              ~f:(fun group -> (group, scope, parameter))
        | _ -> None)
  in
  List.map candidates ~f:(fun (group, scope, parameter) ->
      let declarations =
        List.concat_map scope.Proof_scopes.structure.str_items ~f:(fun item ->
            match item.Typedtree.str_desc with
            | Tstr_type (_, declarations) -> declarations
            | _ -> [])
      in
      let aliases =
        List.filter declarations ~f:(fun declaration ->
            match declaration.Typedtree.typ_kind with
            | Ttype_abstract -> Option.is_some declaration.typ_manifest
            | _ -> false)
      in
      let* aliases =
        List.map aliases ~f:(fun declaration ->
            match
              List.filter group.Generic_modules.representative.declarations
                ~f:(fun other ->
                  String.equal declaration.Typedtree.typ_name.txt
                    other.Typedtree.typ_name.txt)
            with
            | [ other ] when nullary_alias declaration && nullary_alias other ->
                Ok (declaration, other)
            | _ -> Report.unsupported declaration.typ_loc "This generic proof type alias")
        |> Result.all
      in
      Ok { group; scope; parameter; aliases })
  |> Result.all

let owner plans scope =
  Option.bind scope ~f:(fun scope ->
      List.find plans ~f:(fun plan ->
          Option.equal Path.same plan.scope.owner scope.Proof_scopes.owner
          || Option.is_some scope.definition
             && Option.equal Path.same plan.scope.owner scope.parent))

let projection plan =
  List.fold plan.aliases
    ~init:
      (Subst.add_module plan.parameter (Path.Pident plan.group.representative.parameter)
         Subst.identity) ~f:(fun substitution (source, target) ->
      Subst.add_type source.Typedtree.typ_id (Path.Pident target.Typedtree.typ_id)
        substitution)

let types plan =
  let parameters =
    parameter_types plan
      ~owner:(String.split plan.group.name ~on:'.' @ [ plan.group.parameter ])
  in
  let* aliases =
    List.map plan.aliases ~f:(fun (source, _) ->
        let* descriptor = Datatypes.of_declaration source in
        let paths =
          Option.to_list
            (Option.map plan.scope.owner ~f:(fun owner ->
                 Path.Pdot (owner, source.Typedtree.typ_name.txt)))
        in
        Ok (Datatypes.with_paths descriptor paths))
    |> Result.all
  in
  Ok (parameters @ aliases)

let member plan backend = plan.group.name ^ "." ^ backend

let contains plan (binding : Proof_bindings.binding) =
  Option.equal Path.same plan.scope.owner binding.entry.scope.owner

let expand_alias paths (alias, target) =
  let rec replace path =
    if Path.same path target then Some alias
    else
      match path with
      | Path.Pdot (parent, member) ->
          Option.map (replace parent) ~f:(fun parent -> Path.Pdot (parent, member))
      | _ -> None
  in
  paths @ List.filter_map paths ~f:replace

let application_paths (source : Source.t) (inventory : Module_inventory.t)
    (application : Module_inventory.specialization) =
  let paths =
    Proof_scopes.innermost_owners_at source.proof_scopes
      application.argument.site.item_loc
  in
  let aliases =
    List.filter inventory.aliases ~f:(fun (_, target) ->
        not (Path.same target application.identity))
  in
  List.fold aliases ~init:paths ~f:expand_alias
  |> List.dedup_and_sort ~compare:Path.compare

let application_projection source plan (application : Module_inventory.specialization)
    path =
  let actual_parameter =
    match application.identity with
    | Path.Papply (_, argument) -> argument
    | _ -> application.argument.actual_path
  in
  let projection =
    List.fold plan.aliases
      ~init:(Subst.add_module plan.parameter actual_parameter Subst.identity)
      ~f:(fun substitution (original, _) ->
        Subst.add_type original.Typedtree.typ_id
          (Path.Pdot (path, original.typ_name.txt))
          substitution)
  in
  model_projection source plan path projection |> resource_projection source plan path

let applications ~fresh (source : Source.t) (inventory : Module_inventory.t)
    (proofs : Proof_bindings.t) plans =
  let build plan instance =
    let application_source = instance.Generic_modules.source in
    let members =
      List.filter inventory.Module_inventory.values
        ~f:(fun (value : Module_inventory.value) ->
          match value.binding.Typedtree.vb_pat.pat_desc with
          | Tpat_var (id, _, _) ->
              List.exists application_source.members ~f:(fun (_, member) ->
                  Ident.same id member)
          | _ -> false)
    in
    let paths = application_paths source inventory application_source in
    let* private_projection =
      List.fold_result plan.aliases
        ~init:
          (Subst.add_module plan.parameter (Path.Pident application_source.parameter)
             Subst.identity) ~f:(fun substitution (original, _) ->
          match
            List.find application_source.declarations ~f:(fun actual ->
                String.equal actual.Typedtree.typ_name.txt original.Typedtree.typ_name.txt)
          with
          | Some actual ->
              Ok (Subst.add_type original.typ_id (Path.Pident actual.typ_id) substitution)
          | None ->
              Error
                (Report.error Type original.typ_loc
                   "The application has no typed declaration for this proof type alias"))
    in
    let private_projection =
      resource_projection source plan application_source.identity private_projection
    in
    let* environment =
      match members with
      | member :: _ -> Ok (Source.annotation_env source member.site.environment)
      | [] ->
          Error
            (Report.error Type application_source.argument.site.item_loc
               "The application has no typed runtime member for its proof")
    in
    (* Canonical result declarations are shared; agreement uses this typed instance. *)
    let check_projection =
      List.fold application_source.declarations ~init:Subst.identity
        ~f:(fun substitution actual ->
          let path = Path.Pdot (application_source.identity, actual.typ_name.txt) in
          match
            List.find inventory.types ~f:(fun canonical ->
                List.mem canonical.paths path ~equal:Path.same)
          with
          | Some canonical
            when not (Ident.same canonical.declaration.typ_id actual.typ_id) ->
              Subst.add_type canonical.declaration.typ_id (Path.Pident actual.typ_id)
                substitution
          | Some _ | None -> substitution)
    in
    let views =
      List.concat_map paths ~f:(fun path ->
          let projection = application_projection source plan application_source path in
          let project_type = Subst.type_expr projection in
          let constraints =
            List.filter inventory.constraints ~f:(fun constraint_ ->
                Option.exists constraint_.result_owner ~f:(fun owner ->
                    List.exists paths ~f:(Path.same owner)))
          in
          List.filter_map proofs.Proof_bindings.bindings ~f:(fun binding ->
              if not (contains plan binding) then None
              else
                Some
                  Proof_bindings.
                    {
                      source = binding;
                      path;
                      key = fresh (binding.backend ^ "_application");
                      backend = instance.name ^ "." ^ binding.backend;
                      types = List.map binding.private_types ~f:project_type;
                      project_type;
                      implementation_types =
                        List.map binding.private_types
                          ~f:(Subst.type_expr private_projection);
                      environment;
                      check_projection;
                      constraints;
                    }))
    in
    Ok views
  in
  let* views =
    List.concat_map plans ~f:(fun plan ->
        List.map plan.group.applications ~f:(build plan))
    |> Result.all
  in
  Ok (List.concat views)

let model_types source inventory plans =
  List.concat_map plans ~f:(fun plan ->
      let symbolic =
        symbolic_models source plan
          ~owner:(String.split plan.group.name ~on:'.' @ [ "Layout" ])
      in
      let concrete =
        List.concat_map plan.group.applications ~f:(fun instance ->
            let canonical =
              List.find_exn plan.group.applications ~f:(fun other ->
                  Path.same other.source.identity instance.source.identity)
            in
            let paths = application_paths source inventory instance.source in
            List.concat_map paths ~f:(fun path ->
                let project_type =
                  Subst.type_expr
                    (application_projection source plan instance.source path)
                in
                List.map (models source plan) ~f:(fun data ->
                    let representation =
                      model_descriptor data ~owner:[ canonical.layout ]
                    in
                    let paths =
                      Option.value_map data.id ~default:[] ~f:(fun id ->
                          [
                            Path.Pdot (path, Ident.name id);
                            Path.Pdot (instance.source.identity, Ident.name id);
                          ])
                    in
                    {
                      representation with
                      id = None;
                      paths;
                      ctors =
                        List.map data.ctors ~f:(fun ctor ->
                            { ctor with args = List.map ctor.args ~f:project_type });
                    })))
      in
      symbolic @ concrete)

let resource_applications source inventory plans =
  List.concat_map plans ~f:(fun plan ->
      List.concat_map plan.group.applications ~f:(fun instance ->
          let paths = application_paths source inventory instance.source in
          List.concat_map paths ~f:(fun path ->
              let projection = application_projection source plan instance.source path in
              let project_type = Subst.type_expr projection in
              let project_path = Subst.module_path projection in
              List.map (resources source plan) ~f:(fun resource ->
                  let owner = Path.Pdot (path, resource.resource_name) in
                  let rec project (resource : Source.proof_resource) =
                    let leaf =
                      (Qualified_name.of_string resource.resource_backend).name
                    in
                    let backend = instance.name ^ "." ^ leaf in
                    let descriptor member (data : Datatypes.t) =
                      let type_path = Path.Pdot (owner, member) in
                      {
                        data with
                        Datatypes.id = None;
                        library = None;
                        paths =
                          [
                            type_path;
                            Path.Pdot
                              ( Path.Pdot
                                  (instance.source.identity, resource.resource_name),
                                member );
                          ];
                        module_name = backend;
                        module_path = Some (String.split backend ~on:'.');
                        backend_type =
                          Some
                            Qualified_name.
                              { path = String.split backend ~on:'.'; name = "T" };
                        alias = Option.map data.alias ~f:project_type;
                      }
                    in
                    {
                      resource with
                      Source.resource_backend = backend;
                      resource_path = owner;
                      resource_type = project_type resource.resource_type;
                      resource_representation =
                        Option.map resource.resource_representation ~f:project_type;
                      resource_alias_of =
                        Option.map resource.resource_alias_of ~f:project_path;
                      resource_arguments =
                        List.map resource.resource_arguments ~f:(function
                          | Source.Type_argument typ ->
                              Source.Type_argument (project_type typ)
                          | Module_argument path -> Module_argument (project_path path));
                      resource_operations =
                        List.map resource.resource_operations
                          ~f:(fun (name, inputs, output) ->
                            (name, List.map inputs ~f:project_type, project_type output));
                      resource_descriptor = descriptor "t" resource.resource_descriptor;
                      resource_aliases =
                        List.map resource.resource_aliases ~f:(fun alias ->
                            let member =
                              match alias.Datatypes.library with
                              | Some (Path.Pdot (_, member)) -> member
                              | _ -> "element"
                            in
                            descriptor member alias);
                      resource_public = Option.map resource.resource_public ~f:project;
                    }
                  in
                  project resource))))

let layout_dependencies plans (data : Datatypes.t) =
  match data.module_path with
  | Some (layout :: _) ->
      Option.to_list
        (List.find_map plans ~f:(fun plan ->
             List.find_map plan.group.applications ~f:(fun instance ->
                 Option.some_if (String.equal instance.layout layout) layout)))
  | Some [] | None -> []
