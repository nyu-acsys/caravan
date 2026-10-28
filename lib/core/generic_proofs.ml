(** Symbolic proof ownership in generic workers. *)

open Base

let ( let* ) = Result.( >>= )

type t = {
  group : Generic_modules.t;
  scope : Proof_scopes.scope;
  parameter : Ident.t;
  aliases : (Typedtree.type_declaration * Typedtree.type_declaration) list;
}

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
          Option.equal Path.same plan.scope.owner scope.Proof_scopes.owner))

let projection plan =
  List.fold plan.aliases
    ~init:
      (Subst.add_module plan.parameter (Path.Pident plan.group.representative.parameter)
         Subst.identity) ~f:(fun substitution (source, target) ->
      Subst.add_type source.Typedtree.typ_id (Path.Pident target.Typedtree.typ_id)
        substitution)

let types plan =
  let parameters =
    Generic_modules.types plan.group
      ~owner:(String.split plan.group.name ~on:'.' @ [ plan.group.parameter ])
    |> List.map2_exn plan.group.types ~f:(fun (name, _) descriptor ->
        let path = Path.Pdot (Path.Pident plan.parameter, name) in
        { descriptor with Datatypes.id = None; library = Some path; paths = [ path ] })
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

let applications ~fresh (source : Source.t) (inventory : Module_inventory.t)
    (proofs : Proof_bindings.t) plans =
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
  in
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
    let paths =
      Proof_scopes.innermost_owners_at source.proof_scopes
        application_source.argument.site.item_loc
    in
    let aliases =
      List.filter inventory.aliases ~f:(fun (_, target) ->
          not (Path.same target application_source.identity))
    in
    let paths =
      List.fold aliases ~init:paths ~f:expand_alias
      |> List.dedup_and_sort ~compare:Path.compare
    in
    let actual_parameter =
      match application_source.identity with
      | Path.Papply (_, argument) -> argument
      | _ -> application_source.argument.actual_path
    in
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
          let projection =
            List.fold plan.aliases
              ~init:(Subst.add_module plan.parameter actual_parameter Subst.identity)
              ~f:(fun substitution (original, _) ->
                Subst.add_type original.Typedtree.typ_id
                  (Path.Pdot (path, original.typ_name.txt))
                  substitution)
          in
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
