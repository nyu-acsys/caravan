(** Static module declarations and the paths naming their implementation members. *)

open Base

let ( let* ) = Result.( >>= )

type site = {
  environment : Env.t;
  scope : Declaration_scope.t;
  annotations : Annotation.t list;
  item_loc : Location.t;
  next : Location.t option;
}

type signature_value = {
  declaration : Typedtree.value_description;
  site : site;
  substitution : Subst.t;  (** Signature identities qualified for this implementation. *)
  origin_projection : Subst.t;  (** Exported identities in the annotation's source view. *)
}

type value = {
  binding : Typedtree.value_binding;
  namespace : string list;
  site : site;
  paths : Path.t list;
  signatures : signature_value list;
}

type type_definition = {
  declaration : Typedtree.type_declaration;
  namespace : string list;
  paths : Path.t list;
  field_substitution : Subst.t;
}

type field_type = {
  path : Path.t;
  declaration : Types.type_declaration;
  substitution : Subst.t;
  manifest_environment : Env.t option;
}

let field_type_of_definition (definition : type_definition) =
  {
    path = Path.Pident definition.declaration.typ_id;
    declaration = definition.declaration.typ_type;
    substitution = definition.field_substitution;
    manifest_environment =
      Option.map definition.declaration.typ_manifest ~f:(fun manifest ->
          manifest.ctyp_env);
  }

type signature_resource = {
  declaration : Caravan_spec.Spec_ast.predicate;
  declaration_id : Ident.t;
  site : site;
  substitution : Subst.t;
}

type signature_ghost_module = {
  ghost_declaration : Caravan_spec.Spec_ast.ghost_module;
  ghost_resource : Source.proof_resource;
  site : site;
}

type signature_module = {
  signature_id : Ident.t option;
  signature_body : signature_view;
  signature_alias : Path.t option;
}

and signature_view = {
  signature_annotated : bool;
  signature_resources : (string * signature_resource) list;
  signature_ghost_modules : (string * signature_ghost_module) list;
  signature_values : (string * signature_value) list;
  signature_types : (string * Typedtree.type_declaration) list;
  signature_modules : (string * signature_module) list;
  signature_modtypes : (string * signature_view) list;
}

type checked_binding = {
  actual_path : Path.t;
  parameter_substitution : Subst.t;
      (** Concrete type projection for contract compatibility checks. *)
  expected : signature_view;
  site : site;
  namespace : string list;
  paths : Path.t list;
}

type parameter_instance = {
  template : Typedtree.module_expr;
  parameter : Ident.t;
  argument : checked_binding;
}

type specialization = {
  symbolic : bool;
  origin : Path.t option;
  parameters : parameter_instance list;
  context : Functor_context.application option;
  template : Typedtree.module_expr;
  parameter : Ident.t;
  argument : checked_binding;
  members : (string * Ident.t) list;
  body_members : (string * Ident.t) list;
  identity : Path.t;
  declarations : Typedtree.type_declaration list;
}

let function_members (body : Typedtree.structure) =
  let found = ref [] in
  let value_binding iterator (binding : Typedtree.value_binding) =
    (match (binding.vb_pat.pat_desc, binding.vb_expr.exp_desc) with
    | Tpat_var (id, _, _), Texp_function _ ->
        let at = binding.vb_loc in
        let key =
          Printf.sprintf "%s:%d:%d" (Ident.name id) at.loc_start.pos_cnum
            at.loc_end.pos_cnum
        in
        found := (key, id) :: !found
    | _ -> ());
    Tast_iterator.default_iterator.value_binding iterator binding
  in
  let module_expr iterator expression =
    match expression.Typedtree.mod_desc with
    | Tmod_functor _ -> ()
    | _ -> Tast_iterator.default_iterator.module_expr iterator expression
  in
  let iterator = { Tast_iterator.default_iterator with value_binding; module_expr } in
  iterator.structure iterator body;
  List.rev !found

(** The stable body-member key of a value in its original implementation scope. *)
let function_member (scope : Proof_scopes.scope) path =
  let originals = function_members scope.structure in
  let original =
    match path with
    | Path.Pident id ->
        List.find originals ~f:(fun (_, candidate) -> Ident.same id candidate)
    | _ ->
        Option.bind (Source.scoped_value_name scope path) ~f:(fun name ->
            let bindings =
              List.concat_map scope.structure.str_items ~f:(fun item ->
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
  original

let proof_scope_matches (application : specialization) (scope : Proof_scopes.scope) =
  match application.context with
  | Some context -> Functor_context.same_scope scope context.scope
  | None ->
      let rec body expression =
        match expression.Typedtree.mod_desc with
        | Tmod_functor (_, nested) | Tmod_constraint (nested, _, _, _) -> body nested
        | Tmod_structure structure -> Some structure
        | _ -> None
      in
      Option.exists (body application.template) ~f:(fun structure ->
          List.equal
            (fun (left : Typedtree.structure_item) (right : Typedtree.structure_item) ->
              Declaration_scope.same_place left.str_loc right.str_loc)
            scope.structure.str_items structure.str_items)

type resource_constraint = {
  owner : Path.t option;
  result_owner : Path.t option;  (** Source view, distinct from applicative identity. *)
  boundary : Path.t option;
  signature : signature_view;
  substitution : Subst.t;
  at : Location.t;
  restricts_visibility : bool;
}

type t = {
  structure : Typedtree.structure;
  values : value list;
  types : type_definition list;
  aliases : (Path.t * Path.t) list;
  bindings : checked_binding list;
  specializations : specialization list;
  definitions : specialization list;
  constraints : resource_constraint list;
  field_disciplines : Field_disciplines.t list;
  field_origins : (Field_disciplines.t * Field_disciplines.t) list;
  library_signatures : (Source.library * signature_view) list;
}

let same_binding (left : checked_binding) right =
  phys_equal left right
  || Path.same left.actual_path right.actual_path
     && phys_equal left.expected right.expected
     && phys_equal left.parameter_substitution right.parameter_substitution

let formal_binding inventory binding =
  List.exists inventory.definitions ~f:(fun definition ->
      List.exists definition.parameters ~f:(fun parameter ->
          same_binding parameter.argument binding))

let symbolic_binding inventory binding =
  List.exists inventory.specializations ~f:(fun application ->
      application.symbolic
      && List.exists application.parameters ~f:(fun parameter ->
          same_binding parameter.argument binding))

let field_origin inventory ~record_path ~position =
  let rec declaration_path path =
    match path with
    | Path.Pextra_ty (parent, extra) -> Path.Pextra_ty (declaration_path parent, extra)
    | _ ->
        Option.value_map
          (List.find inventory.types ~f:(fun definition ->
               List.mem definition.paths path ~equal:Path.same))
          ~default:path
          ~f:(fun definition -> Path.Pident definition.declaration.typ_id)
  in
  let path = declaration_path record_path in
  List.find_map inventory.field_origins ~f:(fun (alias, origin) ->
      Option.some_if
        (Path.same alias.Field_disciplines.record_path path
        && Int.equal alias.position position)
        origin)

type module_view = {
  functor_definition : functor_definition option;
  checked : checked_binding ref option;
  identity : Path.t option;
  application_identity : Path.t option;
      (** Nominal module identity, independent of the checked operation view. *)
  alias_target : Path.t option;
  values : (string * value ref) list;
  included : value ref list;  (** The values an include of another module binds. *)
  types : (string * type_definition ref) list;
  modules : (string * module_view) list;
  modtypes : (string * signature_view) list;
}

and functor_definition = {
  origin : Path.t option;
  instances : (Typedtree.module_expr * Ident.t * checked_binding ref) list;
  parameter_name : string option;  (** [None] for a unit parameter. *)
  template : Typedtree.module_expr;
  environment : Env.t;
  annotations : Annotation.t list;
  verification : specialization option;
}

type signature_origin = {
  named : Typedtree.module_type_declaration;
  annotations : Annotation.t list;
}

(** The module an include of [expression] names, if it names one by its path. *)
let rec included_path (expression : Typedtree.module_expr) =
  match expression.mod_desc with
  | Tmod_ident (path, _) -> Some path
  | Tmod_constraint (expression, _, _, _) -> included_path expression
  | _ -> None

let rec direct_body (expression : Typedtree.module_expr) =
  match expression.mod_desc with
  | Tmod_structure body -> Some body
  | Tmod_constraint (body, _, _, _) -> direct_body body
  | _ -> None

let empty_signature =
  {
    signature_annotated = false;
    signature_resources = [];
    signature_ghost_modules = [];
    signature_values = [];
    signature_types = [];
    signature_modules = [];
    signature_modtypes = [];
  }

let empty_module =
  {
    functor_definition = None;
    checked = None;
    identity = None;
    application_identity = None;
    alias_target = None;
    values = [];
    included = [];
    types = [];
    modules = [];
    modtypes = [];
  }

let bind bindings name value =
  (name, value) :: List.Assoc.remove bindings name ~equal:String.equal

let member bindings name = List.Assoc.find bindings name ~equal:String.equal

(** Preserve source annotation environments while rebinding an include's exports. *)
let rec include_signature ~at ~environment ~origin_projection substitution expanded
    signature =
  let named find name = List.find_map expanded ~f:(fun item -> find name item) in
  let type_member =
    named (fun name -> function
      | Types.Sig_type (id, declaration, _, _) when String.equal name (Ident.name id) ->
          Some (id, declaration)
      | _ -> None)
  in
  let module_member =
    named (fun name -> function
      | Types.Sig_module (id, _, declaration, _, _) when String.equal name (Ident.name id)
        ->
          Some (id, declaration)
      | _ -> None)
  in
  let modtype_member =
    named (fun name -> function
      | Types.Sig_modtype (id, declaration, _) when String.equal name (Ident.name id) ->
          Some declaration
      | _ -> None)
  in
  let missing name =
    Error (Report.error Type at ("Missing expanded signature member " ^ name))
  in
  let* () =
    match signature.signature_ghost_modules with
    | [] -> Ok ()
    | _ -> Report.unsupported at "An include of a signature with abstract proof modules"
  in
  let* substitution =
    List.fold_result signature.signature_types ~init:substitution
      ~f:(fun substitution (name, declaration) ->
        match type_member name with
        | None -> missing name
        | Some (id, _) ->
            Ok (Subst.add_type declaration.typ_id (Path.Pident id) substitution))
  in
  let origin_projection =
    List.fold signature.signature_types ~init:origin_projection
      ~f:(fun projection (name, declaration) ->
        match type_member name with
        | None -> projection
        | Some (id, _) -> Subst.add_type id (Path.Pident declaration.typ_id) projection)
  in
  let* substitution =
    List.fold_result signature.signature_modules ~init:substitution
      ~f:(fun substitution (name, nested) ->
        match (nested.signature_id, module_member name) with
        | Some old, Some (id, _) ->
            Ok (Subst.add_module old (Path.Pident id) substitution)
        | None, Some _ -> Ok substitution
        | _, None -> missing name)
  in
  let origin_projection =
    List.fold signature.signature_modules ~init:origin_projection
      ~f:(fun projection (name, nested) ->
        match (nested.signature_id, module_member name) with
        | Some old, Some (id, _) -> Subst.add_module id (Path.Pident old) projection
        | None, _ | _, None -> projection)
  in
  let* signature_types =
    List.map signature.signature_types ~f:(fun (name, declaration) ->
        match type_member name with
        | None -> missing name
        | Some (typ_id, typ_type) -> Ok (name, { declaration with typ_id; typ_type }))
    |> Result.all
  in
  let nested body signature =
    match Mtype.scrape environment body with
    | Types.Mty_signature expanded ->
        include_signature ~at ~environment ~origin_projection substitution expanded
          signature
    | _ -> Report.unsupported at "An unexpanded included module signature"
  in
  let* signature_modules =
    List.map signature.signature_modules ~f:(fun (name, signature) ->
        match module_member name with
        | None -> missing name
        | Some (id, declaration) ->
            let* signature_body =
              match signature.signature_alias with
              | Some _ -> Ok signature.signature_body
              | None -> nested declaration.md_type signature.signature_body
            in
            Ok
              ( name,
                {
                  signature_id = Some id;
                  signature_body;
                  signature_alias =
                    Option.map signature.signature_alias
                      ~f:(Subst.module_path substitution);
                } ))
    |> Result.all
  in
  let* signature_modtypes =
    List.map signature.signature_modtypes ~f:(fun (name, signature) ->
        match modtype_member name with
        | Some { mtd_type = Some body; _ } ->
            let* signature = nested body signature in
            Ok (name, signature)
        | Some { mtd_type = None; _ } | None -> missing name)
    |> Result.all
  in
  Ok
    {
      signature with
      signature_types;
      signature_modules;
      signature_modtypes;
      signature_values =
        List.map signature.signature_values ~f:(fun (name, value) ->
            ( name,
              {
                value with
                substitution = Subst.compose value.substitution substitution;
                origin_projection =
                  Subst.compose origin_projection value.origin_projection;
              } ));
      signature_resources =
        List.map signature.signature_resources ~f:(fun (name, resource) ->
            ( name,
              {
                resource with
                declaration_id = Ident.create_local name;
                substitution = Subst.compose resource.substitution substitution;
              } ));
    }

let merge_signature view included =
  let merge left right =
    List.fold right ~init:left ~f:(fun bindings (name, value) -> bind bindings name value)
  in
  {
    signature_annotated = view.signature_annotated || included.signature_annotated;
    signature_values = merge view.signature_values (List.rev included.signature_values);
    signature_types = merge view.signature_types (List.rev included.signature_types);
    signature_resources = merge view.signature_resources included.signature_resources;
    signature_ghost_modules =
      merge view.signature_ghost_modules included.signature_ghost_modules;
    signature_modules = merge view.signature_modules (List.rev included.signature_modules);
    signature_modtypes =
      merge view.signature_modtypes (List.rev included.signature_modtypes);
  }

let add_path paths path =
  if List.mem paths path ~equal:Path.same then paths else paths @ [ path ]

let annotations_in scope children annotations =
  List.filter annotations ~f:(fun (annotation : Annotation.t) ->
      Declaration_scope.contains_in_input scope.Declaration_scope.location annotation.loc
      && not
           (List.exists children ~f:(fun child ->
                Declaration_scope.contains_in_input child annotation.loc)))

let scope location : Declaration_scope.t = { location }

let build (source : Source.t) (structure : Typedtree.structure) :
    (t, Report.error) Result.t =
  let all_values = ref [] in
  let all_types : type_definition ref list ref = ref [] in
  let result_types : (Path.t * type_definition ref) list ref = ref [] in
  let aliases = ref [] in
  let bindings = ref [] in
  let specializations = ref [] in
  let constraints = ref [] in
  let expansions = ref [] in
  let stage_identities = ref [] in
  let parameter_substitution = ref Subst.identity in
  let templates = ref [] in
  let modules = ref [] in
  let modtypes = ref [] in
  let imported_signatures = ref [] in
  let resolving_signatures = ref [] in
  let field_checks = ref [] in
  let check_field_disciplines = Source.visibility_required source in
  let check_fields ~defining ~at ~environment signature actual =
    if check_field_disciplines then
      field_checks :=
        ( defining,
          at,
          environment,
          !parameter_substitution,
          signature.signature_types,
          actual )
        :: !field_checks
  in
  let field_type view name =
    Option.map (List.Assoc.find view.types name ~equal:String.equal) ~f:(fun definition ->
        field_type_of_definition !definition)
  in
  let find_field_type environment path =
    match
      List.find !all_types ~f:(fun definition ->
          Path.same path (Path.Pident !definition.declaration.typ_id)
          || List.mem !definition.paths path ~equal:Path.same)
    with
    | Some definition -> Some (field_type_of_definition !definition)
    | None -> (
        try
          Some
            {
              path;
              declaration = Env.find_type path environment;
              substitution = Subst.identity;
              manifest_environment = None;
            }
        with Stdlib.Not_found -> None)
  in
  let argument_field_type view environment path name =
    match field_type view name with
    | Some _ as definition -> definition
    | None -> find_field_type environment (Path.Pdot (path, name))
  in
  let register registry path value =
    registry := (path, value) :: List.Assoc.remove !registry path ~equal:Path.same
  in
  let lookup registry path = List.Assoc.find !registry path ~equal:Path.same in
  let unavailable at description = Report.unsupported at description in
  let missing at name =
    Error
      (Report.error Unsupported at
         (Printf.sprintf "No static implementation of module member %s" name))
  in
  let rec publish_signature path signature =
    List.iter signature.signature_modtypes ~f:(fun (name, signature) ->
        register modtypes (Path.Pdot (path, name)) signature);
    List.iter signature.signature_modules ~f:(fun (name, nested) ->
        publish_signature (Path.Pdot (path, name)) nested.signature_body)
  in
  let publish_type_paths path view =
    let rec publish path view =
      List.iter view.types ~f:(fun (name, definition) ->
          definition :=
            {
              !definition with
              paths = add_path !definition.paths (Path.Pdot (path, name));
            });
      List.iter view.modules ~f:(fun (name, nested) ->
          publish (Path.Pdot (path, name)) nested)
    in
    publish path view
  in
  let rec publish path view =
    register modules path view;
    Option.iter view.checked ~f:(fun binding ->
        binding := { !binding with paths = add_path !binding.paths path });
    if Option.is_none view.checked then
      Option.iter (Option.first_some view.alias_target view.application_identity)
        ~f:(fun target ->
          if not (Path.same path target) then register aliases path target);
    List.iter view.values ~f:(fun (name, value) ->
        value := { !value with paths = add_path !value.paths (Path.Pdot (path, name)) });
    List.iter view.types ~f:(fun (name, definition) ->
        definition :=
          { !definition with paths = add_path !definition.paths (Path.Pdot (path, name)) });
    List.iter view.modtypes ~f:(fun (name, signature) ->
        register modtypes (Path.Pdot (path, name)) signature);
    List.iter view.modules ~f:(fun (name, nested) ->
        publish (Path.Pdot (path, name)) nested)
  in
  (* An included module's members are its own, under the include's identifiers. *)
  let include_module ~at view included signature =
    List.fold_result signature ~init:view ~f:(fun view (item : Types.signature_item) ->
        let found = function
          | Some member -> Ok member
          | None -> unavailable at "An include of a module without a local implementation"
        in
        match item with
        | Sig_value (id, _, _) ->
            let name = Ident.name id in
            let* value = found (member included.values name) in
            value := { !value with paths = add_path !value.paths (Path.Pident id) };
            Ok
              {
                view with
                values = bind view.values name value;
                included = value :: view.included;
              }
        | Sig_type (id, _, _, _) ->
            let name = Ident.name id in
            begin match member included.types name with
            | Some definition ->
                definition :=
                  { !definition with paths = add_path !definition.paths (Path.Pident id) };
                Ok { view with types = bind view.types name definition }
            | None -> Ok view
            end
        | Sig_module (id, _, _, _, _) ->
            let name = Ident.name id in
            let* nested = found (member included.modules name) in
            publish (Path.Pident id) nested;
            Ok { view with modules = bind view.modules name nested }
        | Sig_modtype (id, _, _) ->
            let name = Ident.name id in
            let* signature = found (member included.modtypes name) in
            register modtypes (Path.Pident id) signature;
            Ok { view with modtypes = bind view.modtypes name signature }
        | Sig_typext _ -> Ok view
        | Sig_class _ | Sig_class_type _ -> unavailable at "An include of a class")
  in
  let resolve_module at env path =
    match lookup modules path with
    | Some view -> Ok view
    | None ->
        let normalized = Env.normalize_module_path None env path in
        begin match lookup modules normalized with
        | Some view -> Ok view
        | None ->
            let rec imported = function
              | Path.Pident id ->
                  List.exists source.libraries ~f:(fun library ->
                      Ident.same id library.Source.library_id)
              | Pdot (parent, _) -> imported parent
              | Papply _ | Pextra_ty _ -> false
            in
            if
              imported normalized
              || Mutex_primitives.is_module normalized
              || Condition_primitives.is_module normalized
            then
              begin try
                let declaration = Env.find_module normalized env in
                match Mtype.scrape env declaration.md_type with
                | Types.Mty_functor _ -> unavailable at "An alias of an imported functor"
                | Mty_signature _ | Mty_ident _ | Mty_alias _ ->
                    Ok
                      {
                        empty_module with
                        identity = Some normalized;
                        application_identity = Some normalized;
                      }
              with exn ->
                Error
                  (Option.value (Report.of_exn exn)
                     ~default:(Report.error Type at (Stdlib.Printexc.to_string exn)))
              end
            else unavailable at "An alias of a module without a local implementation"
        end
  in
  let rec imported_type annotations (mty : Typedtree.module_type) =
    match mty.mty_desc with
    | Tmty_signature signature -> imported_items annotations signature
    | Tmty_ident _ | Tmty_alias _ | Tmty_functor _ | Tmty_with _ | Tmty_typeof _ -> ()
  and imported_items annotations (signature : Typedtree.signature) =
    List.iter signature.sig_items ~f:(fun item ->
        match item.Typedtree.sig_desc with
        | Tsig_modtype named ->
            imported_signatures := { named; annotations } :: !imported_signatures;
            Option.iter named.mtd_type ~f:(imported_type annotations)
        | Tsig_module declaration -> imported_type annotations declaration.md_type
        | Tsig_include declaration -> imported_type annotations declaration.incl_mod
        | _ -> ())
  in
  List.iter source.libraries ~f:(fun library ->
      Option.iter library.Source.library.typed_signature ~f:(fun signature ->
          let annotations = Annotation.of_comments library.library.interface_comments in
          imported_items annotations signature));
  let imported_signature (mty : Typedtree.module_type) path =
    match
      List.find !imported_signatures ~f:(fun origin ->
          Path.same path (Path.Pident origin.named.mtd_id))
    with
    | Some origin -> Ok (Some origin)
    | None ->
        begin try
          let declaration = Env.find_modtype path mty.mty_env in
          Ok
            (List.find !imported_signatures ~f:(fun origin ->
                 Shape.Uid.equal origin.named.mtd_uid declaration.mtd_uid))
        with exn ->
          Error
            (Option.value (Report.of_exn exn)
               ~default:(Report.error Type mty.mty_loc (Stdlib.Printexc.to_string exn)))
        end
  in
  let rec signature_type ~imported annotations (mty : Typedtree.module_type) =
    match mty.mty_desc with
    | Tmty_signature signature ->
        collect_signature ~imported ~shared:imported annotations (scope mty.mty_loc)
          signature
    | Tmty_ident (path, _) ->
        begin match lookup modtypes path with
        | Some signature -> Ok signature
        | None ->
            let normalized = Env.normalize_modtype_path mty.mty_env path in
            begin match lookup modtypes normalized with
            | Some signature -> Ok signature
            | None ->
                let* origin = imported_signature mty path in
                begin match origin with
                | None ->
                    unavailable mty.mty_loc "A module type without a source signature"
                | Some { named = { mtd_type = None; _ }; _ } ->
                    unavailable mty.mty_loc "An abstract imported module type"
                | Some { named; annotations } ->
                    if List.mem !resolving_signatures named.mtd_uid ~equal:Shape.Uid.equal
                    then unavailable mty.mty_loc "A cyclic imported module type"
                    else
                      let previous = !resolving_signatures in
                      resolving_signatures := named.mtd_uid :: previous;
                      let* signature =
                        match named.mtd_type with
                        | Some definition ->
                            signature_type ~imported:true annotations definition
                        | None ->
                            unavailable named.mtd_loc "An abstract imported module type"
                      in
                      resolving_signatures := previous;
                      register modtypes path signature;
                      register modtypes (Path.Pident named.mtd_id) signature;
                      Ok signature
                end
            end
        end
    | Tmty_functor _ -> unavailable mty.mty_loc "A functor signature"
    | Tmty_with _ -> unavailable mty.mty_loc "A module type refinement"
    | Tmty_typeof _ -> unavailable mty.mty_loc "A module type of an expression"
    | Tmty_alias _ -> unavailable mty.mty_loc "An alias in a module signature"
  and collect_signature ~imported ~shared annotations declaration_scope
      (signature : Typedtree.signature) =
    let all_annotations = annotations in
    let children =
      List.filter_map signature.sig_items ~f:(fun (item : Typedtree.signature_item) ->
          match item.sig_desc with
          | Tsig_module declaration -> Some declaration.md_loc
          | Tsig_modtype declaration -> Some declaration.mtd_loc
          | Tsig_include declaration -> Some declaration.incl_loc
          | _ -> None)
    in
    let annotations = annotations_in declaration_scope children annotations in
    let* () =
      List.fold_result annotations ~init:() ~f:(fun () annotation ->
          match Annotation.kind annotation with
          | Contract ->
              let rec attached = function
                | [] -> false
                | (item : Typedtree.signature_item) :: rest ->
                    let next =
                      Option.map (List.hd rest) ~f:(fun item -> item.Typedtree.sig_loc)
                    in
                    (match item.sig_desc with
                      | Tsig_value _ ->
                          Declaration_scope.following ~scope:declaration_scope
                            ~item_loc:item.sig_loc ~next annotation.loc
                      | _ -> false)
                    || attached rest
              in
              if attached signature.sig_items then Ok ()
              else
                Error
                  (Report.error Type annotation.loc
                     "This contract is outside a signature value declaration")
          | Predicate | Ghost_module -> Ok ()
          | Loop when Annotation.invariant_declaration annotation -> Ok ()
          | Loop | Ghost | Scope | Returns | Proof | Manual | Linearization | Initially
          | Initializes | Trusted ->
              if shared then Ok ()
              else
                unavailable annotation.loc
                  "A declaration annotation in a nested module signature")
    in
    let rec items ghost_declarations view = function
      | [] -> Ok view
      | (item : Typedtree.signature_item) :: rest ->
          let raw_environment, next =
            match rest with
            | next :: _ -> (next.sig_env, Some next.sig_loc)
            | [] -> (signature.sig_final_env, None)
          in
          let* environment =
            Proof_types.signature_ghost_environment source ghost_declarations
              raw_environment
          in
          let site =
            {
              environment;
              scope = declaration_scope;
              annotations;
              item_loc = item.sig_loc;
              next;
            }
          in
          let* view =
            match item.sig_desc with
            | Tsig_value declaration ->
                let value =
                  {
                    declaration;
                    site;
                    substitution = Subst.identity;
                    origin_projection = Subst.identity;
                  }
                in
                Ok
                  {
                    view with
                    signature_values =
                      bind view.signature_values declaration.val_name.txt value;
                  }
            | Tsig_type (_, declarations) ->
                Ok
                  {
                    view with
                    signature_types =
                      List.fold declarations ~init:view.signature_types
                        ~f:(fun bindings declaration ->
                          bind bindings declaration.Typedtree.typ_name.txt declaration);
                  }
            | Tsig_module declaration ->
                begin match declaration.md_name.txt with
                | None -> unavailable declaration.md_loc "An anonymous signature module"
                | Some name ->
                    let* nested, signature_alias =
                      match declaration.md_type.mty_desc with
                      | Tmty_alias (path, _) ->
                          let* () =
                            if
                              List.exists all_annotations ~f:(fun annotation ->
                                  Declaration_scope.contains_in_input declaration.md_loc
                                    annotation.Annotation.loc)
                            then
                              unavailable declaration.md_loc
                                "An annotated signature alias"
                            else Ok ()
                          in
                          Ok
                            ( empty_signature,
                              Some
                                (Env.normalize_module_path None
                                   declaration.md_type.mty_env path) )
                      | _ ->
                          let* nested =
                            signature_type ~imported all_annotations declaration.md_type
                          in
                          Ok (nested, None)
                    in
                    Option.iter declaration.md_id ~f:(fun id ->
                        publish_signature (Path.Pident id) nested);
                    Ok
                      {
                        view with
                        signature_modules =
                          bind view.signature_modules name
                            {
                              signature_id = declaration.md_id;
                              signature_body = nested;
                              signature_alias;
                            };
                      }
                end
            | Tsig_modtype declaration ->
                begin match declaration.mtd_type with
                | None -> unavailable declaration.mtd_loc "An abstract module type"
                | Some mty ->
                    let* nested = signature_type ~imported all_annotations mty in
                    register modtypes (Path.Pident declaration.mtd_id) nested;
                    Ok
                      {
                        view with
                        signature_modtypes =
                          bind view.signature_modtypes declaration.mtd_name.txt nested;
                      }
                end
            | Tsig_attribute _ -> Ok view
            | Tsig_open { open_expr = _, _; _ } -> Ok view
            | Tsig_include declaration ->
                let* included =
                  signature_type ~imported all_annotations declaration.incl_mod
                in
                let* included =
                  include_signature ~at:declaration.incl_loc ~environment
                    ~origin_projection:Subst.identity Subst.identity declaration.incl_type
                    included
                in
                let* () =
                  List.fold_result included.signature_resources ~init:()
                    ~f:(fun () (name, _) ->
                      match member view.signature_resources name with
                      | None -> Ok ()
                      | Some _ ->
                          Error
                            (Report.error Type declaration.incl_loc
                               ("The included resource " ^ name ^ " is already declared")))
                in
                List.iter included.signature_modules ~f:(fun (_, nested) ->
                    Option.iter nested.signature_id ~f:(fun id ->
                        publish_signature (Path.Pident id) nested.signature_body));
                List.iter declaration.incl_type ~f:(function
                  | Types.Sig_modtype (id, _, _) ->
                      Option.iter
                        (member included.signature_modtypes (Ident.name id))
                        ~f:(register modtypes (Path.Pident id))
                  | _ -> ());
                Ok (merge_signature view included)
            | Tsig_recmodule _ -> unavailable item.sig_loc "Recursive signature modules"
            | Tsig_typesubst _ | Tsig_modsubst _ | Tsig_modtypesubst _ ->
                unavailable item.sig_loc "A substitution in a module signature"
            | Tsig_exception _ -> Ok view
            | Tsig_typext _ | Tsig_class _ | Tsig_class_type _ ->
                unavailable item.sig_loc "This module signature item"
          in
          items ghost_declarations view rest
    in
    let* signature_resources =
      List.filter annotations ~f:(Annotation.predicate_declaration ~interface:true)
      |> List.map ~f:(fun annotation ->
          let* declaration = Annotation.predicate annotation in
          let* () =
            if shared || Option.is_none declaration.pred_body then Ok ()
            else unavailable annotation.loc "A resource definition in a module signature"
          in
          let environment =
            List.find_map signature.sig_items ~f:(fun item ->
                if
                  item.Typedtree.sig_loc.loc_start.pos_cnum
                  >= annotation.loc.loc_end.pos_cnum
                then Some item.sig_env
                else None)
            |> Option.value ~default:signature.sig_final_env
          in
          let site =
            {
              environment;
              scope = declaration_scope;
              annotations;
              item_loc = annotation.loc;
              next = None;
            }
          in
          Ok
            ( declaration.pred_name.pid_str,
              {
                declaration;
                declaration_id = Ident.create_local declaration.pred_name.pid_str;
                site;
                substitution = Subst.identity;
              } ))
      |> Result.all
    in
    let* () =
      List.fold_result signature_resources ~init:[] ~f:(fun names (name, resource) ->
          if List.mem names name ~equal:String.equal then
            Error
              (Report.error Type resource.site.item_loc
                 ("The signature resource " ^ name ^ " is already declared"))
          else Ok (name :: names))
      |> Result.map ~f:(fun _ -> ())
    in
    let* signature_ghost_modules =
      List.filter annotations ~f:(fun annotation ->
          Poly.equal (Annotation.kind annotation) Ghost_module)
      |> List.fold_result ~init:[] ~f:(fun declarations annotation ->
          let* declaration = Annotation.ghost_module annotation in
          let* ghost_resource = Proof_types.signature_resource source declaration in
          let name = declaration.ghost_module_name.pid_str in
          let at = Caravan_spec.Spec_ast.qualid_loc declaration.ghost_module_interface in
          let* signatures = Proof_library.signatures at in
          let* () =
            let path = Proof_library.path_of_qualid declaration.ghost_module_interface in
            match Proof_library.find signatures path with
            | None ->
                Error
                  (Report.error Type at
                     ("Unknown Raven library interface " ^ String.concat ~sep:"." path))
            | Some selected
              when selected.interface
                   && Proof_library.is_resource_algebra signatures selected ->
                Ok ()
            | Some _ ->
                Error
                  (Report.error Type at
                     "An abstract proof module must name a resource algebra interface")
          in
          let duplicate = List.Assoc.mem declarations name ~equal:String.equal in
          let runtime_module =
            List.exists signature.sig_items ~f:(fun item ->
                match item.Typedtree.sig_desc with
                | Tsig_module member ->
                    Option.equal String.equal member.md_name.txt (Some name)
                | _ -> false)
          in
          let* () =
            if duplicate || runtime_module then
              Error
                (Report.error Type declaration.ghost_module_name.pid_loc
                   (Printf.sprintf "The signature module %s is already declared" name))
            else Ok ()
          in
          let environment =
            List.find_map signature.sig_items ~f:(fun item ->
                if
                  item.Typedtree.sig_loc.loc_start.pos_cnum
                  >= annotation.loc.loc_end.pos_cnum
                then Some item.sig_env
                else None)
            |> Option.value ~default:signature.sig_final_env
          in
          let site =
            {
              environment;
              scope = declaration_scope;
              annotations;
              item_loc = annotation.loc;
              next = None;
            }
          in
          Ok
            ((name, { ghost_declaration = declaration; ghost_resource; site })
            :: declarations))
    in
    let ghost_declarations =
      List.map signature_ghost_modules ~f:(fun (_, ghost) -> ghost.ghost_declaration)
    in
    let* signature_resources =
      List.map signature_resources ~f:(fun (name, resource) ->
          let* environment =
            Proof_types.signature_ghost_environment source ghost_declarations
              resource.site.environment
          in
          Ok (name, { resource with site = { resource.site with environment } }))
      |> Result.all
    in
    let* signature_ghost_modules =
      List.map signature_ghost_modules ~f:(fun (name, ghost) ->
          let* environment =
            Proof_types.signature_ghost_environment source ghost_declarations
              ghost.site.environment
          in
          Ok (name, { ghost with site = { ghost.site with environment } }))
      |> Result.all
    in
    items ghost_declarations
      {
        empty_signature with
        signature_annotated = not (List.is_empty annotations);
        signature_resources;
        signature_ghost_modules;
      }
      signature.sig_items
  in
  let signature_module_substitution substitution path signature =
    List.fold signature.signature_modules ~init:substitution
      ~f:(fun substitution (name, nested) ->
        Option.value_map nested.signature_id ~default:substitution ~f:(fun id ->
            Subst.add_module id (Path.Pdot (path, name)) substitution))
  in
  let rec signature_aliases substitution path signature =
    let substitution = signature_module_substitution substitution path signature in
    List.iter signature.signature_modules ~f:(fun (name, nested) ->
        let path = Path.Pdot (path, name) in
        match nested.signature_alias with
        | Some target -> register aliases path (Subst.module_path substitution target)
        | None -> signature_aliases substitution path nested.signature_body)
  in
  let* library_signatures =
    List.map source.libraries ~f:(fun library ->
        match library.Source.library.typed_signature with
        | None ->
            unavailable library.library.scope.location "An untyped imported signature"
        | Some signature ->
            let* signature =
              collect_signature ~imported:true ~shared:true
                (Annotation.of_comments library.library.interface_comments)
                library.library.scope signature
            in
            let path = Path.Pident library.library_id in
            publish_signature path signature;
            signature_aliases Subst.identity path signature;
            Ok (library, signature))
    |> Result.all
  in
  let rec imported_fields owner (signature : signature_view) =
    let* fields =
      List.map signature.signature_types ~f:(fun (name, declaration) ->
          match declaration.Typedtree.typ_kind with
          | Ttype_record _ ->
              let path = Path.Pdot (owner, name) in
              let* origin_path, origin =
                try
                  let typ = Ctype.newconstr path declaration.typ_type.type_params in
                  let path =
                    match Types.get_desc (Ctype.expand_head source.env typ) with
                    | Tconstr (path, _, _) -> path
                    | _ -> path
                  in
                  Ok (path, Env.find_type path source.env)
                with exn ->
                  Error
                    (Option.value (Report.of_exn exn)
                       ~default:
                         (Report.error Type declaration.typ_loc
                            (Stdlib.Printexc.to_string exn)))
              in
              let* declared =
                Field_disciplines.of_declaration path declaration.typ_type
              in
              let* origins = Field_disciplines.of_declaration origin_path origin in
              List.map declared ~f:(fun field ->
                  match List.find origins ~f:(Field_disciplines.same_slot field) with
                  | None ->
                      unavailable field.at
                        "An imported record field without its declaration"
                  | Some origin ->
                      let* () =
                        if Field_disciplines.shared [ field ] then
                          Field_disciplines.check ~at:field.at ~expected:field
                            ~actual:origin
                        else Ok ()
                      in
                      Ok origin)
              |> Result.all
          | Ttype_abstract | Ttype_variant _ | Ttype_open | Ttype_external _ -> Ok [])
      |> Result.all
    in
    let* nested =
      List.map signature.signature_modules ~f:(fun (name, nested) ->
          match nested.signature_alias with
          | Some _ -> Ok []
          | None -> imported_fields (Path.Pdot (owner, name)) nested.signature_body)
      |> Result.all
    in
    Ok (List.concat fields @ List.concat nested)
  in
  let* imported_field_disciplines =
    List.map library_signatures ~f:(fun (library, signature) ->
        imported_fields (Path.Pident library.Source.library_id) signature)
    |> Result.all |> Result.map ~f:List.concat
  in
  let actual_ghost_resource view name at =
    let rec owner_paths path =
      path
      ::
      (match path with
      | Path.Papply (head, _) -> owner_paths head
      | Pident _ | Pdot _ | Pextra_ty _ -> [])
    in
    let owners =
      List.concat_map
        (List.filter_opt [ view.identity; view.application_identity ])
        ~f:owner_paths
    in
    match
      List.find_map owners ~f:(fun owner ->
          let path = Path.Pdot (owner, name) in
          List.find source.proof_resources ~f:(fun resource ->
              Source.resource_has_path resource path))
    with
    | Some resource -> Ok resource
    | None ->
        Error
          (Report.error Type at
             (Printf.sprintf "The module has no proof resource %s" name))
  in
  let ghost_substitutions ~implementation substitution signature view =
    List.fold_result signature.signature_ghost_modules ~init:substitution
      ~f:(fun substitution (name, ghost) ->
        let* actual = actual_ghost_resource view name ghost.site.item_loc in
        let exposed =
          if implementation then actual
          else Option.value actual.resource_public ~default:actual
        in
        let path =
          if implementation then Path.Pident actual.resource_id else exposed.resource_path
        in
        let substitution =
          Subst.add_module ghost.ghost_resource.resource_id path substitution
        in
        let carrier =
          match Types.get_desc exposed.resource_type with
          | Tconstr (path, [], _) -> path
          | _ -> Path.Pdot (path, "t")
        in
        Ok
          (List.fold ghost.ghost_resource.resource_type_members ~init:substitution
             ~f:(fun substitution (member, id, _) ->
               let path =
                 if String.equal member "T" then carrier
                 else Path.Pdot (path, String.uncapitalize member)
               in
               Subst.add_type id path substitution)))
  in
  let substitutions ?owner ~at substitution signature view =
    let* substitution =
      List.fold_result signature.signature_types ~init:substitution
        ~f:(fun substitution (name, declaration) ->
          match member view.types name with
          | None -> missing declaration.typ_loc name
          | Some definition ->
              Ok
                (Subst.add_type declaration.typ_id
                   (Path.Pident !definition.declaration.typ_id) substitution))
    in
    let* substitution =
      List.fold_result signature.signature_modules ~init:substitution
        ~f:(fun substitution (name, nested) ->
          match member view.modules name with
          | None -> missing at name
          | Some view ->
              let path =
                Option.value_map owner ~default:view.identity ~f:(fun parent ->
                    Some (Path.Pdot (parent, name)))
              in
              Ok
                (match (nested.signature_id, path) with
                | Some id, Some path -> Subst.add_module id path substitution
                | _ -> substitution))
    in
    ghost_substitutions ~implementation:true substitution signature view
  in
  let root_module_path name =
    List.find_map (List.rev structure.str_items) ~f:(fun item ->
        match item.Typedtree.str_desc with
        | Tstr_module { mb_id = Some id; mb_name = { txt = Some member; _ }; _ }
          when String.equal member name ->
            Some (Path.Pident id)
        | _ -> None)
  in
  let rec defining_structure (expression : Typedtree.module_expr) =
    match expression.mod_desc with
    | Tmod_structure structure -> Some structure
    | Tmod_constraint (body, _, _, _) -> defining_structure body
    | _ -> None
  in
  let nested_definition defining name =
    Option.bind defining ~f:(fun (structure : Typedtree.structure) ->
        List.find_map (List.rev structure.str_items) ~f:(fun item ->
            match item.Typedtree.str_desc with
            | Tstr_module { mb_name = { txt = Some member; _ }; mb_expr; _ }
              when String.equal member name ->
                Some (defining_structure mb_expr)
            | _ -> None)
        |> Option.join)
  in
  let declared (site : site) =
    Annotation.contract_after ~scope:site.scope ~item_loc:site.item_loc ~next:site.next
      site.annotations
  in
  let checked_view ?actual_path ~site ~namespace ~paths ~application_identity
      ~parameter_substitution expected actual =
    let* actual_path =
      match Option.first_some actual_path actual.identity with
      | Some path -> Ok path
      | None -> unavailable site.item_loc "A checked module without a static path"
    in
    let binding =
      ref { actual_path; parameter_substitution; expected; site; namespace; paths }
    in
    check_fields ~defining:None ~at:site.item_loc ~environment:site.environment expected
      (argument_field_type actual site.environment actual_path);
    bindings := binding :: !bindings;
    Ok
      {
        empty_module with
        checked = Some binding;
        identity = actual.identity;
        application_identity;
      }
  in
  let rec constrain ~defining ~restricts_visibility ~boundary ~result_owner at
      substitution signature view =
    if Option.is_some view.checked then
      let () =
        Option.iter view.identity ~f:(fun path ->
            check_fields ~defining:None ~at ~environment:source.env signature
              (argument_field_type view source.env path))
      in
      begin match
        ( signature.signature_ghost_modules,
          signature.signature_resources,
          signature.signature_values )
      with
      | (_, ghost) :: _, _, _ ->
          unavailable ghost.site.item_loc
            "An abstract proof module constraint on a checked module view"
      | [], (_, resource) :: _, _ ->
          unavailable resource.site.item_loc
            "A resource-bearing interface constraint on a checked module view"
      | [], [], (_, value) :: _ ->
          unavailable value.site.item_loc
            "An additional interface contract on a checked module view"
      | [], [], [] -> Ok view
      end
    else
      let* substitution =
        substitutions
          ?owner:(if restricts_visibility then None else result_owner)
          ~at substitution signature view
      in
      check_fields ~defining ~at ~environment:source.env signature (field_type view);
      let* checked_export =
        if restricts_visibility || Option.is_none result_owner then Ok false
        else
          List.map signature.signature_values ~f:(fun (name, _) ->
              match member view.values name with
              | None -> Ok false
              | Some value ->
                  let* contracts =
                    List.map
                      (!value.site :: List.map !value.signatures ~f:(fun s -> s.site))
                      ~f:declared
                    |> Result.all
                  in
                  Ok (List.exists contracts ~f:Option.is_some))
          |> Result.all
          |> Result.map ~f:(List.exists ~f:Fn.id)
      in
      (* Checked exports carry their resources independently of the implementation. *)
      if not checked_export then
        constraints :=
          {
            owner = Option.first_some view.application_identity view.identity;
            result_owner;
            boundary;
            signature;
            substitution;
            at;
            restricts_visibility;
          }
          :: !constraints;
      let* values =
        List.map signature.signature_values ~f:(fun (name, signature_value) ->
            match member view.values name with
            | None -> missing signature_value.site.item_loc name
            | Some value ->
                let* expected = declared signature_value.site in
                let* own = declared !value.site in
                let* previous =
                  List.map !value.signatures ~f:(fun signature -> declared signature.site)
                  |> Result.all
                in
                let* () =
                  List.fold_result
                    (Option.to_list own @ List.filter_opt previous)
                    ~init:()
                    ~f:(fun () (actual, annotation) ->
                      Callable_contract.check ~at
                        ~related:[ (annotation.loc, "Its other contract") ]
                        ~expected:(Option.map expected ~f:fst) ~actual:(Some actual) ())
                in
                let declarations =
                  List.map signature.signature_ghost_modules ~f:(fun (_, ghost) ->
                      ghost.ghost_declaration)
                in
                let* environment =
                  Proof_types.realize_signature_ghost_environment source ~substitution
                    declarations signature_value.site.environment
                in
                let signature_value =
                  {
                    signature_value with
                    substitution = Subst.compose signature_value.substitution substitution;
                    site = { signature_value.site with environment };
                  }
                in
                (* Existing declarations are the implementation of a checked export, as
                   are those of an included module. *)
                let implemented =
                  Option.is_some own || List.exists previous ~f:Option.is_some
                in
                let included = List.mem view.included value ~equal:phys_equal in
                let* () =
                  match expected with
                  | Some (_, annotation) when included && implemented ->
                      Error
                        (Report.error Type annotation.loc
                           "A signature cannot give another contract to an included \
                            function")
                  | _ -> Ok ()
                in
                if not ((checked_export || included) && implemented) then
                  value :=
                    { !value with signatures = !value.signatures @ [ signature_value ] };
                Ok (name, value))
        |> Result.all
      in
      let* types =
        List.map signature.signature_types ~f:(fun (name, declaration) ->
            match member view.types name with
            | None -> missing declaration.typ_loc name
            | Some definition -> Ok (name, definition))
        |> Result.all
      in
      let* nested_modules =
        List.map signature.signature_modules ~f:(fun (name, signature) ->
            match member view.modules name with
            | None -> missing at name
            | Some view ->
                begin match signature.signature_alias with
                | Some _ -> Ok (name, view)
                | None ->
                    let* result_owner =
                      match result_owner with
                      | Some parent -> Ok (Some (Path.Pdot (parent, name)))
                      | None ->
                          begin match root_module_path name with
                          | Some path -> Ok (Some path)
                          | None -> missing at name
                          end
                    in
                    let* view =
                      constrain
                        ~defining:(nested_definition defining name)
                        ~restricts_visibility ~boundary ~result_owner at substitution
                        signature.signature_body view
                    in
                    Ok (name, view)
                end)
        |> Result.all
      in
      let constrained =
        {
          view with
          values;
          types;
          modules = nested_modules;
          modtypes = signature.signature_modtypes;
        }
      in
      if not checked_export then Ok constrained
      else
        let path = Option.value_exn result_owner in
        let site =
          {
            environment = source.env;
            scope = scope at;
            annotations = [];
            item_loc = at;
            next = None;
          }
        in
        let* checked =
          checked_view ~actual_path:path ~site
            ~namespace:(String.split (Path.name path) ~on:'.')
            ~paths:[ path ] ~application_identity:view.application_identity
            ~parameter_substitution:substitution signature view
        in
        Ok { constrained with checked = checked.checked }
  in
  let apply_signature ~defining ~restricts_visibility ~result_owner at signature view =
    constrain ~defining ~restricts_visibility ~boundary:result_owner ~result_owner at
      Subst.identity signature view
  in
  let seal_application_identity path signature view =
    let rec identities substitution path signature =
      let substitution = signature_module_substitution substitution path signature in
      List.concat_map signature.signature_modules ~f:(fun (name, nested) ->
          let path = Path.Pdot (path, name) in
          let target =
            Option.value_map nested.signature_alias ~default:path
              ~f:(Subst.module_path substitution)
          in
          (path, target) :: identities substitution path nested.signature_body)
    in
    let identities = (path, path) :: identities Subst.identity path signature in
    let rec canonical path =
      match List.Assoc.find identities path ~equal:Path.same with
      | Some target -> if Path.same target path then path else canonical target
      | None ->
          begin match lookup modules path with
          | Some view -> Option.value view.application_identity ~default:path
          | None ->
              begin match path with
              | Path.Pdot (parent, name) -> Path.Pdot (canonical parent, name)
              | Papply (head, argument) -> Path.Papply (canonical head, canonical argument)
              | Pident _ | Pextra_ty _ -> path
              end
          end
    in
    let rec seal path view =
      let target = canonical path in
      let modules =
        List.map view.modules ~f:(fun (name, nested) ->
            (name, seal (Path.Pdot (target, name)) nested))
      in
      {
        view with
        application_identity = Some target;
        alias_target = Option.some_if (not (Path.same path target)) target;
        modules;
      }
    in
    seal path view
  in
  let rec effective env at mty view =
    match Mtype.scrape env mty with
    | Types.Mty_signature signature ->
        let* result =
          List.fold_result signature ~init:empty_module ~f:(fun result -> function
            | Types.Sig_value (id, _, _) ->
                begin match member view.values (Ident.name id) with
                | None -> missing at (Ident.name id)
                | Some value ->
                    Ok { result with values = bind result.values (Ident.name id) value }
                end
            | Sig_type (id, _, _, _) ->
                begin match member view.types (Ident.name id) with
                | None -> missing at (Ident.name id)
                | Some definition ->
                    Ok
                      { result with types = bind result.types (Ident.name id) definition }
                end
            | Sig_module (id, _, declaration, _, _) ->
                begin match member view.modules (Ident.name id) with
                | None -> missing at (Ident.name id)
                | Some nested ->
                    let* nested = effective env at declaration.md_type nested in
                    Ok
                      { result with modules = bind result.modules (Ident.name id) nested }
                end
            | Sig_modtype (id, _, _) ->
                begin match member view.modtypes (Ident.name id) with
                | None -> missing at (Ident.name id)
                | Some signature ->
                    Ok
                      {
                        result with
                        modtypes = bind result.modtypes (Ident.name id) signature;
                      }
                end
            | Sig_typext _ | Sig_class _ | Sig_class_type _ ->
                unavailable at "This constrained module signature item")
        in
        Ok
          {
            result with
            identity = view.identity;
            application_identity = view.application_identity;
            checked = view.checked;
          }
    | Mty_alias path -> resolve_module at env path
    | Mty_functor _ -> unavailable at "A functor signature"
    | Mty_ident _ -> unavailable at "An abstract module signature"
  in
  let rec module_expression ~definitions ~captures annotations namespace ~identity
      (expression : Typedtree.module_expr) =
    match expression.mod_desc with
    | Tmod_structure structure ->
        collect_structure ~definitions ~captures annotations namespace ~identity
          (scope expression.mod_loc) structure
    | Tmod_ident (path, _) ->
        let* view = resolve_module expression.mod_loc expression.mod_env path in
        Ok
          {
            view with
            alias_target = Some (Env.normalize_module_path None expression.mod_env path);
          }
    | Tmod_constraint (body, mty, annotation, _) ->
        let rec alias (expression : Typedtree.module_expr) =
          match expression.mod_desc with
          | Tmod_ident _ -> true
          | Tmod_constraint (body, _, _, _) -> alias body
          | _ -> false
        in
        if alias body then
          let* actual =
            module_expression ~definitions ~captures annotations namespace ~identity body
          in
          begin match annotation with
          | Tmodtype_implicit -> Ok actual
          | Tmodtype_explicit mty ->
              let* () =
                match actual.checked with
                | Some binding when List.is_empty !binding.paths ->
                    unavailable expression.mod_loc
                      "Nested inline constraints on a checked module view"
                | Some _ | None -> Ok ()
              in
              let* expected = signature_type ~imported:false annotations mty in
              let* () =
                if List.is_empty expected.signature_modules then Ok ()
                else
                  unavailable expression.mod_loc "Nested modules in a checked module view"
              in
              let site =
                {
                  environment = expression.mod_env;
                  scope = scope expression.mod_loc;
                  annotations;
                  item_loc = expression.mod_loc;
                  next = None;
                }
              in
              checked_view ~site ~namespace ~paths:[] ~application_identity:identity
                ~parameter_substitution:!parameter_substitution expected actual
          end
        else
          let* view =
            module_expression ~definitions ~captures annotations namespace ~identity body
          in
          begin match annotation with
          | Tmodtype_explicit mty ->
              let* signature = signature_type ~imported:false annotations mty in
              let* view =
                apply_signature ~defining:(defining_structure body)
                  ~restricts_visibility:true ~result_owner:identity mty.mty_loc signature
                  view
              in
              Ok
                (Option.value_map identity ~default:view ~f:(fun path ->
                     seal_application_identity path signature view))
          | Tmodtype_implicit ->
              if Option.is_some view.functor_definition then Ok view
              else effective expression.mod_env expression.mod_loc mty view
          end
    | Tmod_functor _ ->
        let rec parameters (expression : Typedtree.module_expr) =
          match expression.mod_desc with
          | Tmod_functor (parameter, body) ->
              let* parameter_name =
                match parameter with
                | Unit -> Ok None
                | Named (Some _, { txt = Some name; _ }, parameter_type) ->
                    let* parameter_view =
                      signature_type ~imported:false annotations parameter_type
                    in
                    let* () =
                      if List.is_empty parameter_view.signature_modules then Ok ()
                      else
                        unavailable parameter_type.mty_loc
                          "Nested modules in a functor parameter"
                    in
                    let* () =
                      List.fold_result parameter_view.signature_values ~init:()
                        ~f:(fun () (_, value) ->
                          match
                            Types.get_desc
                              (Ctype.expand_head value.site.environment
                                 value.declaration.val_val.val_type)
                          with
                          | Types.Tarrow _ -> Ok ()
                          | _ ->
                              unavailable value.site.item_loc
                                "A non-function value in a functor parameter")
                    in
                    Ok (Some name)
                | Named (None, _, _) | Named (Some _, { txt = None; _ }, _) ->
                    unavailable expression.mod_loc "An anonymous functor parameter"
              in
              let* body =
                match body.mod_desc with
                | Tmod_functor _ -> Result.map (parameters body) ~f:snd
                | _ ->
                    if Option.is_some (direct_body body) then Ok body
                    else
                      unavailable body.mod_loc "A functor without a direct structure body"
              in
              Ok (parameter_name, body)
          | _ -> unavailable expression.mod_loc "A non-structural functor declaration"
        in
        let* parameter_name, body = parameters expression in
        let* () =
          let valid = ref (Ok ()) in
          let type_declaration iterator declaration =
            valid :=
              Result.bind !valid ~f:(fun () ->
                  Result.map (Datatypes.of_declaration declaration) ~f:(fun _ -> ()));
            Tast_iterator.default_iterator.type_declaration iterator declaration
          in
          let iterator =
            {
              Tast_iterator.default_iterator with
              type_declaration;
              module_type = (fun _ _ -> ());
            }
          in
          iterator.module_expr iterator body;
          !valid
        in
        let* verification =
          match (definitions, identity) with
          | false, _ | _, None -> Ok None
          | true, Some identity ->
              let rec formal_parameters stages (template : Typedtree.module_expr) =
                match template.mod_desc with
                | Tmod_functor (parameter, body) ->
                    let* parameter, parameter_name, expected =
                      match parameter with
                      | Unit -> Ok (Ident.create_local "Unit", "Unit", empty_signature)
                      | Named (Some id, { txt = Some name; _ }, mty) ->
                          let* expected =
                            signature_type ~imported:false annotations mty
                          in
                          Ok (id, name, expected)
                      | Named _ ->
                          unavailable template.mod_loc "An anonymous functor parameter"
                    in
                    let path = Path.Pident parameter in
                    check_fields ~defining:None ~at:template.mod_loc
                      ~environment:body.mod_env expected
                      (argument_field_type empty_module body.mod_env path);
                    let argument =
                      {
                        actual_path = path;
                        parameter_substitution = Subst.identity;
                        expected;
                        site =
                          {
                            environment = body.mod_env;
                            scope = scope template.mod_loc;
                            annotations;
                            item_loc = template.mod_loc;
                            next = None;
                          };
                        namespace = namespace @ [ parameter_name ];
                        paths = [ path ];
                      }
                    in
                    let binding = ref argument in
                    bindings := binding :: !bindings;
                    publish path
                      {
                        empty_module with
                        checked = Some binding;
                        identity = Some path;
                        application_identity = Some path;
                      };
                    let stages =
                      stages @ [ { template; parameter; argument = !binding } ]
                    in
                    begin match body.mod_desc with
                    | Tmod_functor _ -> formal_parameters stages body
                    | _ ->
                        let* view =
                          module_expression ~definitions ~captures:stages annotations
                            namespace ~identity:(Some identity) body
                        in
                        publish_type_paths identity view;
                        let declarations, body_members =
                          match direct_body body with
                          | Some body ->
                              ( List.concat_map body.str_items ~f:(fun item ->
                                    match item.Typedtree.str_desc with
                                    | Tstr_type (_, declarations) -> declarations
                                    | _ -> []),
                                function_members body )
                          | None -> ([], [])
                        in
                        Ok
                          (Some
                             {
                               symbolic = true;
                               origin = Some identity;
                               parameters = stages;
                               context = None;
                               template;
                               parameter;
                               argument = !binding;
                               members =
                                 List.filter_map view.values ~f:(fun (name, value) ->
                                     match !value.binding.vb_pat.pat_desc with
                                     | Tpat_var (id, _, _) -> Some (name, id)
                                     | _ -> None);
                               body_members;
                               identity;
                               declarations;
                             })
                    end
                | _ -> unavailable template.mod_loc "A non-structural functor declaration"
              in
              formal_parameters captures expression
        in
        Ok
          {
            empty_module with
            application_identity = identity;
            functor_definition =
              Some
                {
                  origin = identity;
                  instances = [];
                  parameter_name;
                  template = expression;
                  environment = expression.mod_env;
                  annotations;
                  verification;
                };
          }
    | Tmod_apply (callee, argument, _) ->
        specialize
          ~symbolic:(definitions && not (List.is_empty captures))
          annotations namespace ~identity expression callee (Some argument)
    | Tmod_apply_unit callee ->
        specialize
          ~symbolic:(definitions && not (List.is_empty captures))
          annotations namespace ~identity expression callee None
    | Tmod_unpack _ -> unavailable expression.mod_loc "A first-class module"
  and specialize ~symbolic annotations namespace ~identity
      (expression : Typedtree.module_expr) callee argument =
    let rec application_head (value : Typedtree.module_expr) =
      match value.mod_desc with
      | Tmod_constraint (body, _, Tmodtype_implicit, _) -> application_head body
      | _ -> value
    in
    let static_path description (value : Typedtree.module_expr) =
      match (application_head value).mod_desc with
      | Tmod_ident (path, _) -> Ok path
      | _ -> unavailable value.mod_loc description
    in
    let callee = application_head callee in
    let* template =
      match callee.mod_desc with
      | Tmod_ident _ ->
          let* path = static_path "A non-path functor application" callee in
          resolve_module expression.mod_loc expression.mod_env path
      | Tmod_apply _ | Tmod_apply_unit _ ->
          let* stage_identity =
            match identity with
            | None ->
                unavailable callee.mod_loc
                  "A functor application without a result binding"
            | Some enclosing ->
                begin match
                  List.find !stage_identities ~f:(fun (root, at, _) ->
                      Path.same root enclosing
                      && Declaration_scope.same_in_input at callee.mod_loc)
                with
                | Some (_, _, identity) -> Ok identity
                | None ->
                    let identity = Path.Pident (Ident.create_local "functor_stage") in
                    stage_identities :=
                      (enclosing, callee.mod_loc, identity) :: !stage_identities;
                    Ok identity
                end
          in
          module_expression ~definitions:false ~captures:[] annotations namespace
            ~identity:(Some stage_identity) callee
      | _ -> unavailable callee.mod_loc "A non-path functor application"
    in
    let* definition =
      match template.functor_definition with
      | Some definition -> Ok definition
      | None -> unavailable expression.mod_loc "An application of an unavailable functor"
    in
    let* actual =
      match argument with
      | None -> Ok None
      | Some argument ->
          let* path = static_path "A non-path functor argument" argument in
          let* actual = resolve_module argument.mod_loc argument.mod_env path in
          let* actual_path =
            match (actual.identity, actual.functor_definition) with
            | Some path, None -> Ok path
            | _ -> unavailable argument.mod_loc "A higher-order functor argument"
          in
          Ok (Some (actual, actual_path))
    in
    let registered_stage =
      List.find_map source.proof_applications ~f:(fun application ->
          List.find application.Functor_context.stages ~f:(fun stage ->
              Poly.equal stage.Functor_context.location expression.mod_loc))
    in
    let* application_identity =
      match registered_stage with
      | Some stage -> Ok stage.identity
      | None -> (
          match (definition.parameter_name, actual, identity) with
          | None, None, Some identity -> Ok identity
          | Some _, Some (actual, _), _ ->
              begin match
                (template.application_identity, actual.application_identity)
              with
              | Some head, Some argument -> Ok (Path.Papply (head, argument))
              | _ ->
                  unavailable expression.mod_loc
                    "A functor application without an identity"
              end
          | None, None, None ->
              unavailable expression.mod_loc "A unit application without a result binding"
          | None, Some _, _ | Some _, None, _ ->
              unavailable expression.mod_loc
                "A functor application with the wrong parameter shape")
    in
    let* parameter, body =
      try
        let mapper = Untypeast.default_mapper in
        let parsed = mapper.module_expr mapper definition.template in
        let template, _ = Typemod.type_module definition.environment parsed in
        match template.mod_desc with
        | Tmod_functor (parameter, body) -> Ok (parameter, body)
        | _ -> unavailable expression.mod_loc "A non-structural functor specialization"
      with exn ->
        Error
          (Option.value (Report.of_exn exn)
             ~default:
               (Report.error Type expression.mod_loc (Stdlib.Printexc.to_string exn)))
    in
    let* argument_binding =
      match (parameter, definition.parameter_name, actual) with
      | Unit, None, None ->
          let parameter = Ident.create_local "Unit" in
          let binding =
            ref
              {
                actual_path = application_identity;
                parameter_substitution = !parameter_substitution;
                expected = empty_signature;
                site =
                  {
                    environment = expression.mod_env;
                    scope = scope expression.mod_loc;
                    annotations;
                    item_loc = expression.mod_loc;
                    next = None;
                  };
                namespace = namespace @ [ "Unit" ];
                paths = [ Path.Pident parameter ];
              }
          in
          bindings := binding :: !bindings;
          Ok (Some (parameter, binding))
      | ( Named (Some parameter, _, parameter_type),
          Some parameter_name,
          Some (actual, actual_path) ) ->
          let* expected =
            signature_type ~imported:false definition.annotations parameter_type
          in
          check_fields ~defining:None ~at:expression.mod_loc
            ~environment:expression.mod_env expected
            (argument_field_type actual expression.mod_env actual_path);
          let* substitution =
            ghost_substitutions ~implementation:false !parameter_substitution expected
              actual
          in
          let parameter_path = Path.Pident parameter in
          parameter_substitution :=
            Subst.add_module parameter
              (Subst.module_path substitution actual_path)
              substitution;
          let environment =
            Env.add_module ~noalias:true parameter Types.Mp_present
              parameter_type.mty_type expression.mod_env
          in
          let binding =
            ref
              {
                actual_path;
                parameter_substitution = !parameter_substitution;
                expected;
                site =
                  {
                    environment;
                    scope = scope expression.mod_loc;
                    annotations;
                    item_loc = expression.mod_loc;
                    next = None;
                  };
                namespace = namespace @ [ parameter_name ];
                paths = [];
              }
          in
          bindings := binding :: !bindings;
          publish parameter_path
            {
              empty_module with
              checked = Some binding;
              identity = Some parameter_path;
              application_identity = actual.application_identity;
            };
          Ok (Some (parameter, binding))
      | _ ->
          unavailable expression.mod_loc
            "A functor specialization with the wrong parameter shape"
    in
    let* view =
      module_expression ~definitions:false ~captures:[] definition.annotations namespace
        ~identity:(Some application_identity) body
    in
    let instances =
      definition.instances
      @ Option.to_list
          (Option.map argument_binding ~f:(fun (parameter, binding) ->
               (definition.template, parameter, binding)))
    in
    let view =
      {
        view with
        functor_definition =
          Option.map view.functor_definition ~f:(fun inner ->
              { inner with instances; origin = definition.origin });
      }
    in
    if Option.is_none view.functor_definition then begin
      publish_type_paths application_identity view;
      expansions := (expression, body) :: !expansions;
      Option.iter argument_binding ~f:(fun (parameter, binding) ->
          let declarations, body_members =
            match direct_body body with
            | Some body ->
                ( List.concat_map body.str_items ~f:(fun item ->
                      match item.Typedtree.str_desc with
                      | Tstr_type (_, declarations) -> declarations
                      | _ -> []),
                  function_members body )
            | None -> ([], [])
          in
          specializations :=
            ( symbolic,
              definition.template,
              parameter,
              binding,
              view.values,
              application_identity,
              declarations,
              body_members,
              instances,
              definition.origin,
              Functor_context.find_at source.proof_applications expression.mod_loc )
            :: !specializations)
    end;
    Ok view
  and collect_structure ~definitions ~captures annotations namespace ~identity
      declaration_scope (structure : Typedtree.structure) =
    let all_annotations = annotations in
    let children =
      List.filter_map structure.str_items ~f:(fun (item : Typedtree.structure_item) ->
          match item.str_desc with
          | Tstr_module declaration -> Some declaration.mb_loc
          | Tstr_modtype declaration -> Some declaration.mtd_loc
          | _ -> None)
    in
    let annotations = annotations_in declaration_scope children annotations in
    let* () =
      List.fold_result annotations ~init:() ~f:(fun () annotation ->
          match Annotation.kind annotation with
          | Predicate when not (List.is_empty namespace) ->
              unavailable annotation.loc "A predicate declaration in a nested module"
          | Contract ->
              let rec attached = function
                | [] -> false
                | (item : Typedtree.structure_item) :: rest ->
                    let next =
                      Option.map (List.hd rest) ~f:(fun item -> item.Typedtree.str_loc)
                    in
                    (match item.str_desc with
                      | Tstr_value (_, bindings) ->
                          Declaration_scope.following ~scope:declaration_scope
                            ~item_loc:item.str_loc ~next annotation.loc
                          || List.exists bindings ~f:(fun binding ->
                              Declaration_scope.contains_in_input
                                binding.Typedtree.vb_expr.exp_loc annotation.loc)
                      | _ -> false)
                    || attached rest
              in
              if attached structure.str_items then Ok ()
              else
                Error
                  (Report.error Type annotation.loc
                     "This contract is outside a function declaration")
          | Ghost_module ->
              unavailable annotation.loc
                "An abstract proof module outside a module signature"
          | Predicate | Loop | Ghost | Scope | Returns | Proof | Manual | Linearization
          | Initially | Initializes | Trusted ->
              Ok ())
    in
    let rec items view = function
      | [] -> Ok view
      | (item : Typedtree.structure_item) :: rest ->
          let environment, next =
            match rest with
            | next :: _ -> (next.str_env, Some next.str_loc)
            | [] -> (structure.str_final_env, None)
          in
          let site =
            {
              environment;
              scope = declaration_scope;
              annotations;
              item_loc = item.str_loc;
              next;
            }
          in
          let* view =
            match item.str_desc with
            | Tstr_type (_, declarations) ->
                let types =
                  List.fold declarations ~init:view.types ~f:(fun bindings declaration ->
                      let path = Path.Pident declaration.typ_id in
                      let key =
                        Option.value_map identity ~default:path ~f:(fun parent ->
                            Path.Pdot (parent, declaration.typ_name.txt))
                      in
                      let definition =
                        match lookup result_types key with
                        | Some definition ->
                            definition :=
                              { !definition with paths = add_path !definition.paths path };
                            definition
                        | None ->
                            let definition =
                              ref
                                {
                                  declaration;
                                  namespace;
                                  paths = [ path; key ];
                                  field_substitution = !parameter_substitution;
                                }
                            in
                            register result_types key definition;
                            all_types := definition :: !all_types;
                            definition
                      in
                      bind bindings declaration.typ_name.txt definition)
                in
                Ok { view with types }
            | Tstr_value (_, bindings) ->
                let values =
                  List.fold bindings ~init:view.values ~f:(fun values binding ->
                      let id =
                        match binding.Typedtree.vb_pat.pat_desc with
                        | Tpat_var (id, _, _) -> Some id
                        | _ -> None
                      in
                      let value =
                        ref
                          {
                            binding;
                            namespace;
                            site;
                            paths =
                              Option.to_list (Option.map id ~f:(fun id -> Path.Pident id));
                            signatures = [];
                          }
                      in
                      all_values := value :: !all_values;
                      match id with
                      | None -> values
                      | Some id -> bind values (Ident.name id) value)
                in
                Ok { view with values }
            | Tstr_module declaration ->
                begin match (declaration.mb_id, declaration.mb_name.txt) with
                | Some id, Some name ->
                    let* nested =
                      let identity =
                        Some
                          (Option.value_map identity ~default:(Path.Pident id)
                             ~f:(fun parent -> Path.Pdot (parent, name)))
                      in
                      module_expression ~definitions ~captures all_annotations
                        (namespace @ [ name ]) ~identity declaration.mb_expr
                    in
                    begin match declaration.mb_expr.mod_desc with
                    | Tmod_ident _ -> ()
                    | _ ->
                        Option.iter nested.checked ~f:(fun binding ->
                            binding :=
                              { !binding with site = { !binding.site with environment } })
                    end;
                    let nested =
                      match declaration.mb_expr.mod_desc with
                      | Tmod_ident _ -> nested
                      | _ -> { nested with identity = Some (Path.Pident id) }
                    in
                    if Option.is_some nested.functor_definition then
                      templates := id :: !templates;
                    publish (Path.Pident id) nested;
                    Ok { view with modules = bind view.modules name nested }
                | _ -> unavailable declaration.mb_loc "An anonymous module binding"
                end
            | Tstr_modtype declaration ->
                begin match declaration.mtd_type with
                | None -> unavailable declaration.mtd_loc "An abstract module type"
                | Some mty ->
                    let* signature = signature_type ~imported:false all_annotations mty in
                    register modtypes (Path.Pident declaration.mtd_id) signature;
                    Ok
                      {
                        view with
                        modtypes = bind view.modtypes declaration.mtd_name.txt signature;
                      }
                end
            | Tstr_attribute _ -> Ok view
            | Tstr_open { open_expr = { mod_desc = Tmod_ident _; _ }; _ } -> Ok view
            | Tstr_open _ -> unavailable item.str_loc "An open of a module expression"
            | Tstr_include { incl_mod; incl_type; _ } ->
                begin match included_path incl_mod with
                | None -> unavailable item.str_loc "An include of a module expression"
                | Some path ->
                    let* included = resolve_module item.str_loc environment path in
                    include_module ~at:item.str_loc view included incl_type
                end
            | Tstr_recmodule _ -> unavailable item.str_loc "Recursive module bindings"
            | Tstr_eval _ -> unavailable item.str_loc "A module initializer"
            | Tstr_primitive _ -> unavailable item.str_loc "An external value declaration"
            (* Exceptions are the constructors of one type; see [Exceptions]. *)
            | Tstr_exception _ -> Ok view
            | Tstr_typext _ | Tstr_class _ | Tstr_class_type _ ->
                unavailable item.str_loc "This module structure item"
          in
          items view rest
    in
    items { empty_module with application_identity = identity } structure.str_items
  in
  let* view =
    collect_structure ~definitions:true ~captures:[] (Source.annotations source) []
      ~identity:None source.scope structure
  in
  let* () =
    match source.interface with
    | None -> Ok ()
    | Some interface ->
        begin match interface.typed_signature with
        | None -> unavailable interface.scope.location "An untyped module interface"
        | Some typed ->
            let* signature =
              collect_signature ~imported:false ~shared:true
                (Annotation.of_comments interface.interface_comments)
                interface.scope typed
            in
            let* _ =
              apply_signature ~defining:(Some structure) ~restricts_visibility:false
                ~result_owner:None interface.scope.location signature view
            in
            Ok ()
        end
  in
  (* Companion predicates complete signatures without proof annotations. *)
  let constraints =
    let constraints = List.rev !constraints in
    let companion =
      List.filter constraints ~f:(fun constraint_ -> not constraint_.restricts_visibility)
    in
    let rec unannotated signature =
      (not signature.signature_annotated)
      && List.for_all signature.signature_modules ~f:(fun (_, nested) ->
          unannotated nested.signature_body)
      && List.for_all signature.signature_modtypes ~f:(fun (_, nested) ->
          unannotated nested)
    in
    let rec overlay owner signature =
      if not (unannotated signature) then signature
      else
        let resources =
          List.find_map companion ~f:(fun constraint_ ->
              Option.some_if (Option.equal Path.same owner constraint_.owner) constraint_)
          |> Option.value_map ~default:signature.signature_resources
               ~f:(fun constraint_ ->
                 List.map constraint_.signature.signature_resources
                   ~f:(fun (name, resource) ->
                     ( name,
                       {
                         resource with
                         substitution =
                           Subst.compose resource.substitution constraint_.substitution;
                       } )))
        in
        let modules =
          List.map signature.signature_modules ~f:(fun (name, nested) ->
              let owner =
                Option.value_map owner ~default:(root_module_path name) ~f:(fun owner ->
                    Some (Path.Pdot (owner, name)))
              in
              (name, { nested with signature_body = overlay owner nested.signature_body }))
        in
        { signature with signature_resources = resources; signature_modules = modules }
    in
    List.map constraints ~f:(fun constraint_ ->
        if constraint_.restricts_visibility then
          { constraint_ with signature = overlay constraint_.owner constraint_.signature }
        else constraint_)
  in
  let definitions =
    let current_binding binding =
      Option.value_map
        (Option.bind (lookup modules binding.actual_path) ~f:(fun view -> view.checked))
        ~default:binding
        ~f:(fun current -> !current)
    in
    List.filter_map (List.rev !modules) ~f:(fun (_, view) ->
        Option.bind view.functor_definition ~f:(fun definition -> definition.verification))
    |> List.stable_dedup ~compare:(fun (left : specialization) right ->
        Path.compare left.identity right.identity)
    |> List.map ~f:(fun definition ->
        {
          definition with
          argument = current_binding definition.argument;
          parameters =
            List.map definition.parameters ~f:(fun stage ->
                { stage with argument = current_binding stage.argument });
        })
  in
  let field_aliases = ref [] in
  let rec project_path substitutions seen path =
    let projected =
      List.fold substitutions ~init:path ~f:(fun path substitution ->
          Subst.type_path substitution path)
    in
    if Path.same path projected || List.mem seen projected ~equal:Path.same then path
    else project_path substitutions (path :: seen) projected
  in
  let rec field_layout environment substitutions seen
      ({ path; declaration; substitution; manifest_environment } : field_type) =
    let open Types in
    let substitutions = substitution :: substitutions in
    let* declared = Field_disciplines.of_declaration path declaration in
    match Option.map declaration.type_manifest ~f:get_desc with
    | Some (Tconstr (origin, _, _)) ->
        let origin = project_path substitutions [] origin in
        let seen = path :: seen in
        let definition =
          if List.mem seen origin ~equal:Path.same then None
          else
            match find_field_type environment origin with
            | Some _ as definition -> definition
            | None ->
                Option.bind manifest_environment ~f:(fun environment ->
                    find_field_type environment origin)
        in
        begin match definition with
        | None ->
            begin match declared with
            | [] -> Ok []
            | field :: _ ->
                Report.unsupported field.at
                  "A record alias with an unresolved field origin"
            end
        | Some definition ->
            let* inherited = field_layout environment substitutions seen definition in
            List.iter declared ~f:(fun field ->
                Option.iter
                  (List.find inherited ~f:(Field_disciplines.same_slot field))
                  ~f:(fun origin -> field_aliases := (field, origin) :: !field_aliases));
            Ok inherited
        end
    | _ -> Ok declared
  in
  let* comparisons =
    List.rev !field_checks
    |> List.map ~f:(fun (defining, at, environment, substitution, declarations, actual) ->
        List.map declarations
          ~f:(fun (name, (declaration : Typedtree.type_declaration)) ->
            let* expected =
              field_layout environment [ substitution ] []
                {
                  path = Path.Pident declaration.typ_id;
                  declaration = declaration.typ_type;
                  substitution = Subst.identity;
                  manifest_environment =
                    Option.map declaration.typ_manifest ~f:(fun manifest ->
                        manifest.ctyp_env);
                }
            in
            match expected with
            | [] -> Ok []
            | _ ->
                let* definition =
                  match actual name with
                  | Some definition -> Ok definition
                  | None -> missing at name
                in
                let can_define =
                  match definition with
                  | {
                   path = Path.Pident id;
                   declaration = { type_manifest = None; _ };
                   _;
                  } ->
                      Option.exists defining ~f:(fun structure ->
                          List.Assoc.mem
                            (Source.source_type_ids structure)
                            id ~equal:Ident.same)
                  | _ -> false
                in
                let* actual = field_layout environment [ substitution ] [] definition in
                let* fields =
                  List.map expected ~f:(fun expected ->
                      match
                        List.find actual ~f:(fun actual ->
                            Field_disciplines.same_slot expected actual)
                      with
                      | Some actual ->
                          Ok
                            ( can_define,
                              at,
                              Option.is_some declaration.typ_type.type_manifest,
                              expected,
                              actual )
                      | None -> missing at expected.label)
                  |> Result.all
                in
                Ok fields)
        |> Result.all)
    |> Result.all
    |> Result.map ~f:(fun checks -> List.concat_map checks ~f:List.concat)
  in
  let* () =
    if not check_field_disciplines then Ok ()
    else
      List.fold_result !all_types ~init:() ~f:(fun () definition ->
          let declaration = !definition.declaration in
          match (declaration.typ_manifest, declaration.typ_kind) with
          | Some manifest, (Ttype_record _ | Ttype_variant _) ->
              Result.map
                (field_layout manifest.ctyp_env [] []
                   (field_type_of_definition !definition))
                ~f:(fun _ -> ())
          | _ -> Ok ())
  in
  let projections =
    List.filter_map comparisons ~f:(fun (can_define, _, inherited, expected, actual) ->
        if
          (not inherited)
          && Poly.equal actual.kind Field_disciplines.Ordinary
          && Field_disciplines.shared [ expected ]
          && can_define
        then Some (actual.label_id, expected)
        else None)
  in
  let projected (field : Field_disciplines.t) =
    match List.Assoc.find projections field.label_id ~equal:Ident.same with
    | None -> field
    | Some declaration ->
        { field with kind = declaration.kind; raw = declaration.raw; at = declaration.at }
  in
  let effective (field : Field_disciplines.t) =
    match
      List.find !field_aliases ~f:(fun (alias, _) ->
          Ident.same alias.Field_disciplines.label_id field.label_id)
    with
    | None -> projected field
    | Some (_, origin) ->
        let origin = projected origin in
        { field with kind = origin.kind; raw = origin.raw; at = origin.at }
  in
  let* () =
    List.fold_result !field_aliases ~init:() ~f:(fun () (expected, actual) ->
        if Field_disciplines.shared [ expected ] then
          Field_disciplines.check ~at:expected.at ~expected ~actual:(projected actual)
        else Ok ())
  in
  let* () =
    List.fold_result comparisons ~init:()
      ~f:(fun () (_, at, inherited, expected, actual) ->
        Field_disciplines.check ~at
          ~expected:(if inherited then effective expected else expected)
          ~actual:(effective actual))
  in
  Ok
    {
      definitions;
      structure =
        (let module_expr mapper expression =
           match List.Assoc.find !expansions expression ~equal:phys_equal with
           | Some body -> Tast_mapper.default.module_expr mapper body
           | None -> Tast_mapper.default.module_expr mapper expression
         in
         let map_structure mapper structure =
           let str_items =
             List.filter_map structure.Typedtree.str_items ~f:(fun item ->
                 match item.Typedtree.str_desc with
                 | Tstr_module ({ mb_id = Some id; _ } as declaration)
                   when List.mem !templates id ~equal:Ident.same ->
                     let definition =
                       Option.bind (lookup modules (Path.Pident id)) ~f:(fun view ->
                           Option.bind view.functor_definition ~f:(fun d ->
                               d.verification))
                     in
                     Option.map definition ~f:(fun definition ->
                         let rec body (expression : Typedtree.module_expr) =
                           match expression.mod_desc with
                           | Tmod_functor (_, nested) | Tmod_constraint (nested, _, _, _)
                             ->
                               body nested
                           | _ -> expression
                         in
                         {
                           item with
                           str_desc =
                             Tstr_module
                               { declaration with mb_expr = body definition.template };
                         })
                 | _ -> Some item)
           in
           Tast_mapper.default.structure mapper { structure with str_items }
         in
         let mapper =
           { Tast_mapper.default with module_expr; structure = map_structure }
         in
         mapper.structure mapper structure);
      values = List.rev_map !all_values ~f:(fun value -> !value);
      types = List.rev_map !all_types ~f:(fun definition -> !definition);
      aliases = List.rev !aliases;
      bindings = List.rev_map !bindings ~f:(fun binding -> !binding);
      constraints;
      field_disciplines =
        List.map (source.field_disciplines @ imported_field_disciplines) ~f:effective
        |> List.stable_dedup ~compare:(fun left right ->
            let order =
              Path.compare left.Field_disciplines.record_path
                right.Field_disciplines.record_path
            in
            if order = 0 then Int.compare left.position right.position else order);
      field_origins =
        List.map !field_aliases ~f:(fun (alias, origin) -> (alias, projected origin));
      library_signatures;
      specializations =
        List.rev_map !specializations
          ~f:(fun
              ( symbolic,
                template,
                parameter,
                argument,
                values,
                identity,
                declarations,
                body_members,
                instances,
                origin,
                context )
            ->
            {
              symbolic;
              origin;
              parameters =
                List.map instances ~f:(fun (template, parameter, argument) ->
                    { template; parameter; argument = !argument });
              context;
              template;
              parameter;
              argument = !argument;
              identity;
              declarations;
              body_members;
              members =
                List.filter_map values ~f:(fun (member, value) ->
                    match !value.binding.vb_pat.pat_desc with
                    | Tpat_var (id, _, _) -> Some (member, id)
                    | _ -> None);
            });
    }
