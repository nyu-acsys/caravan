(** Imported signature namespaces, with their compiler paths and source scopes. *)

open Base

let ( let* ) = Result.( >>= )

type t = {
  library_name : string;
  library_id : Ident.t;
  library_path : Path.t;
  source_name : string;
  library : Source.interface;
  signature : Module_inventory.signature_view;
  projection : Subst.t;
}

let environment (source : Source.t) library =
  let lexical =
    Option.value_map library.library.typed_signature ~default:source.env
      ~f:(fun signature -> signature.Typedtree.sig_final_env)
  in
  let rec root = function
    | Path.Pident id -> id
    | Pdot (parent, _) -> root parent
    | Papply _ | Pextra_ty _ -> library.library_id
  in
  let root = root library.library_path in
  let declaration = Env.find_module (Pident root) source.env in
  let lexical =
    Env.add_module_declaration ~check:false root Mp_present declaration lexical
  in
  let lexical = Source.annotation_env source lexical in
  match Env.open_signature Asttypes.Override library.library_path lexical with
  | Ok environment -> Ok environment
  | Error (`Not_found | `Functor) ->
      Error
        (Report.error Type library.library.scope.location
           ("Cannot resolve imported module " ^ library.source_name))

(** Source declarations retain the compiler variables of parameterized abstract types. *)
let abstract_types library =
  List.map library.signature.signature_types ~f:(fun (_, declaration) ->
      match (declaration.Typedtree.typ_kind, declaration.typ_manifest) with
      | Ttype_abstract, None -> Ok declaration
      | _ ->
          Report.unsupported declaration.typ_loc
            "A library type other than an abstract type")
  |> Result.all

let value library (value : Module_inventory.signature_value) =
  { value with substitution = Subst.compose value.substitution library.projection }

(** Imported contract references retain the identity of their source declaration. *)
let value_paths library =
  Path_bindings.of_list
    (List.map library.signature.signature_values ~f:(fun (name, value) ->
         let declaration = value.Module_inventory.declaration in
         (Path.Pident declaration.val_id, Path.Pdot (library.library_path, name))))

let resource_type library (resource : Module_inventory.signature_resource) typ =
  Subst.type_expr library.projection (Subst.type_expr resource.substitution typ)

let flatten libraries =
  let owner_projection path (signature : Module_inventory.signature_view) substitution =
    let substitution =
      List.fold signature.signature_types ~init:substitution
        ~f:(fun substitution (name, declaration) ->
          Subst.add_type declaration.Typedtree.typ_id
            (Path.Pdot (path, name))
            substitution)
    in
    let substitution =
      List.fold signature.signature_modules ~init:substitution
        ~f:(fun substitution (name, nested) ->
          let path = Path.Pdot (path, name) in
          Option.value_map nested.signature_id ~default:substitution ~f:(fun id ->
              Subst.add_module id path substitution))
    in
    List.fold signature.signature_ghost_modules ~init:substitution
      ~f:(fun substitution (name, ghost) ->
        let owner = Path.Pdot (path, name) in
        let project substitution resource =
          let substitution =
            Subst.add_module resource.Source.resource_id owner substitution
          in
          List.fold resource.resource_type_members ~init:substitution
            ~f:(fun substitution (member, id, _) ->
              Subst.add_type id
                (Path.Pdot (owner, String.uncapitalize member))
                substitution)
        in
        let resource = ghost.Module_inventory.ghost_resource in
        let substitution = project substitution resource in
        Option.value_map resource.resource_public ~default:substitution
          ~f:(project substitution))
  in
  let rec namespace ~library_name ~library_id ~library_path ~source_name ~projection
      library (signature : Module_inventory.signature_view) =
    (* Inventory bindings are newest first; imports emit declaration order. *)
    let signature =
      {
        signature with
        signature_values = List.rev signature.signature_values;
        signature_types = List.rev signature.signature_types;
        signature_modules = List.rev signature.signature_modules;
        signature_modtypes = List.rev signature.signature_modtypes;
      }
    in
    let projection = owner_projection library_path signature projection in
    let current =
      {
        library_name;
        library_id;
        library_path;
        source_name;
        library;
        signature;
        projection;
      }
    in
    let* children =
      List.map signature.signature_modules ~f:(fun (name, nested) ->
          match nested.signature_alias with
          | Some _ -> Ok []
          | None ->
              let source_name = source_name ^ "." ^ name in
              let library_name =
                Fresh_names.fresh (String.tr source_name ~target:'.' ~replacement:'_')
              in
              namespace ~library_name
                ~library_id:(Ident.create_local library_name)
                ~library_path:(Path.Pdot (library_path, name))
                ~source_name ~projection library nested.signature_body)
      |> Result.all
    in
    Ok (current :: List.concat children)
  in
  List.map libraries ~f:(fun ((library : Source.library), signature) ->
      let library_path = Path.Pident library.library_id in
      namespace ~library_name:library.library_name ~library_id:library.library_id
        ~library_path ~source_name:library.library_name ~projection:Subst.identity
        library.library signature)
  |> Result.all |> Result.map ~f:List.concat
