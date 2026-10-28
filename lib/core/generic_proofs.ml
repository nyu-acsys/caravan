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
