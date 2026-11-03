(** Symbolic proof ownership in generic workers. *)

open Base

let ( let* ) = Result.( >>= )

type parameter = {
  original : Ident.t option;
  instance : Module_inventory.parameter_instance;
  generic : Generic_modules.t;
}

type t = {
  group : Generic_modules.t;
  scope : Proof_scopes.scope;
  parameters : parameter list;
  aliases : (Typedtree.type_declaration * Typedtree.type_declaration) list;
}

let runtime_types plan =
  List.concat_map plan.scope.structure.str_items ~f:(fun item ->
      match item.Typedtree.str_desc with
      | Tstr_type (_, declarations) -> declarations
      | _ -> [])

let matching_type declaration declarations =
  List.find declarations ~f:(fun actual ->
      String.equal declaration.Typedtree.typ_name.txt actual.Typedtree.typ_name.txt
      && Poly.equal declaration.typ_loc actual.typ_loc)

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

let rec expand_type_head environment typ =
  let expanded = Ctype.expand_head environment typ in
  match Types.get_desc expanded with
  | Tconstr (path, arguments, _) ->
      Ctype.newconstr path (List.map arguments ~f:(expand_type_head environment))
  | Ttuple fields ->
      Btype.newgenty
        (Ttuple
           (List.map fields ~f:(fun (label, field) ->
                (label, expand_type_head environment field))))
  | Tarrow (label, argument, result, mode) ->
      Btype.newgenty
        (Tarrow
           ( label,
             expand_type_head environment argument,
             expand_type_head environment result,
             mode ))
  | Tpoly (body, variables) ->
      Btype.newgenty (Tpoly (expand_type_head environment body, variables))
  | _ -> expanded

let scope_matches scope application =
  Module_inventory.proof_scope_matches application scope

let has_models source specialization =
  List.exists source.Source.proof_types ~f:(fun data ->
      Option.exists (model_owner source data) ~f:(fun scope ->
          scope_matches scope specialization))

let model_descriptor data ~owner =
  let path = owner @ [ data.Datatypes.module_name ] in
  {
    data with
    module_path = Some path;
    cell_namespace = Some owner;
    backend_type = Some Qualified_name.{ path; name = "T" };
  }

let symbolic_models source plan ~owner =
  List.map (models source plan) ~f:(fun data -> model_descriptor data ~owner)

let parameter_pairs plan =
  List.filter_map plan.parameters ~f:(fun parameter ->
      Option.map parameter.original ~f:(fun original ->
          (original, parameter.instance.parameter)))

let source_parameters plan = List.map (parameter_pairs plan) ~f:fst

let parameter_types ?(world = false) plan ~owner =
  List.concat_map plan.parameters ~f:(fun parameter ->
      let generic = parameter.generic in
      let descriptors =
        (if world then Generic_modules.world_types else Generic_modules.types)
          generic ~owner:(owner generic)
      in
      match parameter.original with
      | None -> descriptors
      | Some original ->
          let formal_types, ghost_types =
            List.split_n descriptors (List.length generic.types)
          in
          let formal_types =
            List.map2_exn generic.types formal_types ~f:(fun (name, _) descriptor ->
                let path = Path.Pdot (Path.Pident original, name) in
                {
                  descriptor with
                  Datatypes.id = None;
                  library = Some path;
                  paths = [ path ];
                })
          in
          let ghost_types =
            List.map2_exn generic.representative.argument.expected.signature_ghost_modules
              ghost_types ~f:(fun (name, _) descriptor ->
                Datatypes.with_paths descriptor
                  [ Path.Pdot (Path.Pdot (Path.Pident original, name), "t") ])
          in
          formal_types @ ghost_types)

let parameter_substitution plan target =
  List.foldi plan.parameters ~init:Subst.identity ~f:(fun index substitution parameter ->
      Option.value_map parameter.original ~default:substitution ~f:(fun original ->
          Subst.add_module original (target index parameter) substitution))

let application_substitution plan (application : Module_inventory.specialization) =
  match application.context with
  | Some context -> Functor_context.substitution context
  | None ->
      parameter_substitution plan (fun index _ ->
          (List.nth_exn application.parameters index).argument.actual_path)

let private_substitution plan (application : Module_inventory.specialization) =
  parameter_substitution plan (fun index _ ->
      Path.Pident (List.nth_exn application.parameters index).parameter)

let model_projection source plan path substitution =
  List.fold (models source plan) ~init:substitution ~f:(fun substitution data ->
      Option.value_map data.Datatypes.id ~default:substitution ~f:(fun id ->
          Subst.add_type id (Path.Pdot (path, Ident.name id)) substitution))

let asset_projection source plan path substitution =
  let substitution =
    match plan.scope.owner with
    | Some (Path.Pident id) -> Subst.add_module id path substitution
    | Some (Pdot _ | Papply _ | Pextra_ty _) | None -> substitution
  in
  let substitution =
    List.fold (resources source plan) ~init:substitution ~f:(fun substitution resource ->
        let owner = Path.Pdot (path, resource.resource_name) in
        let add_resource substitution resource =
          let substitution =
            Subst.add_module resource.Source.resource_id owner substitution
          in
          List.fold resource.resource_type_members ~init:substitution
            ~f:(fun substitution (member, id, _) ->
              Subst.add_type id
                (Path.Pdot (owner, String.uncapitalize member))
                substitution)
        in
        let substitution = add_resource substitution resource in
        Option.value_map resource.resource_public ~default:substitution
          ~f:(add_resource substitution))
  in
  List.fold source.Source.proof_aus ~init:substitution ~f:(fun substitution au ->
      if
        Option.is_none au.Source.au_application
        && Option.equal Path.same au.au_scope plan.scope.owner
      then Subst.add_module au.au_id (Path.Pdot (path, au.au_name)) substitution
      else substitution)

let manifest_alias (declaration : Typedtree.type_declaration) =
  match declaration.typ_kind with
  | Ttype_abstract -> Option.is_some declaration.typ_manifest
  | _ -> false

let plan groups scopes =
  let candidates =
    List.filter_map scopes.Proof_scopes.scopes ~f:(fun scope ->
        if List.is_empty scope.parameters then None
        else
          Option.map
            (List.find groups ~f:(fun group ->
                 scope_matches scope group.Generic_modules.representative))
            ~f:(fun group -> (group, scope)))
  in
  List.map candidates ~f:(fun (group, scope) ->
      let parameters =
        List.map2_exn scope.parameters
          (List.zip_exn group.Generic_modules.representative.parameters
             (Generic_modules.parameter_groups group))
          ~f:(fun original (instance, generic) ->
            let original =
              match original with
              | Typedtree.Named (Some id, _, _) -> Some id
              | Unit | Named (None, _, _) -> None
            in
            { original; instance; generic })
      in
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
            | [ other ]
              when manifest_alias declaration && manifest_alias other
                   && List.length declaration.typ_params = List.length other.typ_params ->
                Ok (declaration, other)
            | _ -> Report.unsupported declaration.typ_loc "This generic proof type alias")
        |> Result.all
      in
      Ok { group; scope; parameters; aliases })
  |> Result.all

let owner plans scope =
  Option.bind scope ~f:(fun scope ->
      List.find plans ~f:(fun plan ->
          Option.equal Path.same plan.scope.owner scope.Proof_scopes.owner
          || Option.is_some scope.definition
             && Option.equal Path.same plan.scope.owner scope.parent))

let projection plan =
  List.fold (runtime_types plan)
    ~init:
      (parameter_substitution plan (fun _ parameter ->
           Path.Pident parameter.instance.parameter))
    ~f:(fun substitution source ->
      Option.value_map (matching_type source plan.group.representative.declarations)
        ~default:substitution ~f:(fun target ->
          Subst.add_type source.Typedtree.typ_id (Path.Pident target.Typedtree.typ_id)
            substitution))

let source_projection plan =
  List.fold (runtime_types plan)
    ~init:
      (List.fold (parameter_pairs plan) ~init:Subst.identity
         ~f:(fun substitution (original, target) ->
           Subst.add_module target (Path.Pident original) substitution))
    ~f:(fun substitution source ->
      Option.value_map (matching_type source plan.group.representative.declarations)
        ~default:substitution ~f:(fun target ->
          Subst.add_type target.Typedtree.typ_id (Path.Pident source.Typedtree.typ_id)
            substitution))

let types plan =
  let parameters =
    parameter_types plan ~owner:(fun generic ->
        String.split plan.group.name ~on:'.' @ [ generic.Generic_modules.parameter ])
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
  let projection =
    List.fold (runtime_types plan) ~init:(application_substitution plan application)
      ~f:(fun substitution original ->
        Subst.add_type original.Typedtree.typ_id
          (Path.Pdot (path, original.typ_name.txt))
          substitution)
  in
  model_projection source plan path projection |> asset_projection source plan path

let implementation_projection (application : Module_inventory.specialization) path =
  let substitution =
    List.fold application.Module_inventory.parameters ~init:Subst.identity
      ~f:(fun substitution parameter ->
        Subst.add_module parameter.parameter parameter.argument.actual_path substitution)
  in
  List.fold application.declarations ~init:substitution
    ~f:(fun substitution declaration ->
      Subst.add_type declaration.Typedtree.typ_id
        (Path.Pdot (path, declaration.typ_name.txt))
        substitution)

let function_id plan ?(instance = plan.group.Generic_modules.representative) path =
  let originals = Module_inventory.function_members plan.scope.structure in
  let original =
    match path with
    | Path.Pident id ->
        List.find originals ~f:(fun (_, candidate) -> Ident.same id candidate)
    | _ ->
        Option.bind (Source.scoped_value_name plan.scope path) ~f:(fun name ->
            let bindings =
              List.concat_map plan.scope.structure.str_items ~f:(fun item ->
                  match item.Typedtree.str_desc with
                  | Tstr_value (_, bindings) -> bindings
                  | _ -> [])
            in
            let id =
              List.find_map (List.rev bindings) ~f:(fun binding ->
                  match binding.Typedtree.vb_pat.pat_desc with
                  | Tpat_var (id, _, _) when String.equal name (Ident.name id) -> Some id
                  | _ -> None)
            in
            Option.bind id ~f:(fun id ->
                List.find originals ~f:(fun (_, candidate) -> Ident.same id candidate)))
  in
  Option.bind original ~f:(fun (key, _) ->
      List.Assoc.find instance.body_members key ~equal:String.equal)

let applications (source : Source.t) (inventory : Module_inventory.t)
    (proofs : Proof_bindings.t) plans =
  let build plan instance =
    let application_source = instance.Generic_modules.source in
    let members =
      List.filter inventory.Module_inventory.values
        ~f:(fun (value : Module_inventory.value) ->
          match value.binding.Typedtree.vb_pat.pat_desc with
          | Tpat_var (id, _, _) ->
              List.exists application_source.body_members ~f:(fun (_, member) ->
                  Ident.same id member)
          | _ -> false)
    in
    let paths = application_paths source inventory application_source in
    let* private_projection =
      List.fold_result (runtime_types plan)
        ~init:(private_substitution plan application_source)
        ~f:(fun substitution original ->
          match matching_type original application_source.declarations with
          | Some actual ->
              Ok (Subst.add_type original.typ_id (Path.Pident actual.typ_id) substitution)
          | None ->
              Error
                (Report.error Type original.typ_loc
                   "The application has no typed declaration for this proof type alias"))
    in
    let* environment =
      match members with
      | member :: _ -> Ok (Source.annotation_env source member.site.environment)
      | [] ->
          Error
            (Report.error Type application_source.argument.site.item_loc
               "The application has no typed runtime member for its proof")
    in
    let private_projection =
      asset_projection source plan application_source.identity private_projection
    in
    let* private_projection =
      List.fold_result (resources source plan) ~init:private_projection
        ~f:(fun projection template ->
          let application =
            List.find source.proof_resources ~f:(fun resource ->
                Option.exists resource.Source.resource_application
                  ~f:(fun (identity, member) ->
                    Path.same identity application_source.identity
                    && Ident.same member template.resource_id))
          in
          match application with
          | None -> Ok projection
          | Some application ->
              let* carrier =
                Signature_contract.compiler ~at:template.resource_at (fun () ->
                    Ctype.expand_head application.resource_environment
                      (Ctype.newconstr
                         (Path.Pdot (Path.Pident application.resource_id, "t"))
                         []))
              in
              begin match Types.get_desc carrier with
              | Tconstr (carrier, [], _) ->
                  Ok
                    (List.fold template.resource_type_members ~init:projection
                       ~f:(fun projection (member, id, _) ->
                         if String.equal member "T" then
                           Subst.add_type id carrier projection
                         else projection))
              | _ -> Ok projection
              end)
    in
    let* private_types =
      List.map proofs.Proof_bindings.bindings ~f:(fun binding ->
          if not (contains plan binding) then Ok (binding.backend, [])
          else
            let* types =
              List.map binding.private_types ~f:(fun typ ->
                  Signature_contract.compiler ~at:binding.entry.name.pid_loc (fun () ->
                      expand_type_head binding.environment typ))
              |> Result.all
            in
            Ok (binding.backend, types))
      |> Result.all
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
                    Path.same application_source.identity owner
                    || List.exists paths ~f:(Path.same owner)))
          in
          List.filter_map proofs.Proof_bindings.bindings ~f:(fun binding ->
              if not (contains plan binding) then None
              else
                Some
                  Proof_bindings.
                    {
                      source = binding;
                      path;
                      key = Fresh_names.fresh (binding.backend ^ "_application");
                      backend = instance.name ^ "." ^ binding.backend;
                      types = List.map binding.private_types ~f:project_type;
                      project_type;
                      implementation_types =
                        List.map
                          (List.Assoc.find_exn private_types binding.backend
                             ~equal:String.equal)
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
                    let components =
                      data.parameters @ Option.to_list data.alias
                      @ List.concat_map data.ctors ~f:(fun ctor -> ctor.Datatypes.args)
                    in
                    let projected =
                      match components with
                      | [] -> []
                      | _ ->
                          let packed =
                            Btype.newgenty
                              (Ttuple (List.map components ~f:(fun typ -> (None, typ))))
                          in
                          begin match Types.get_desc (project_type packed) with
                          | Ttuple fields -> List.map fields ~f:snd
                          | _ ->
                              failwith
                                "A module substitution must preserve tuple structure"
                          end
                    in
                    let parameters, projected =
                      List.split_n projected (List.length data.parameters)
                    in
                    let alias, projected =
                      match data.alias with
                      | None -> (None, projected)
                      | Some _ -> (Some (List.hd_exn projected), List.tl_exn projected)
                    in
                    let _, ctors =
                      List.fold_map data.ctors ~init:projected ~f:(fun projected ctor ->
                          let args, rest =
                            List.split_n projected (List.length ctor.args)
                          in
                          (rest, { ctor with args }))
                    in
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
                    { representation with id = None; paths; parameters; alias; ctors })))
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
                  let resource = Source.map_resource_types resource ~f:project_type in
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
                      }
                    in
                    {
                      resource with
                      Source.resource_backend = backend;
                      resource_path = owner;
                      resource_application =
                        Some (instance.source.identity, resource.resource_id);
                      resource_alias_of =
                        Option.map resource.resource_alias_of ~f:project_path;
                      resource_arguments =
                        List.map resource.resource_arguments ~f:(function
                          | Source.Type_argument _ as argument -> argument
                          | Module_argument path -> Module_argument (project_path path));
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
