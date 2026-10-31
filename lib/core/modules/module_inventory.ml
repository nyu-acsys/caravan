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
}

type signature_resource = {
  declaration : Caravan_spec.Spec_ast.predicate;
  declaration_id : Ident.t;
  site : site;
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
  let iterator = { Tast_iterator.default_iterator with value_binding } in
  iterator.structure iterator body;
  List.rev !found

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
  constraints : resource_constraint list;
}

type module_view = {
  functor_definition : functor_definition option;
  checked : checked_binding ref option;
  identity : Path.t option;
  application_identity : Path.t option;
      (** Nominal module identity, independent of the checked operation view. *)
  alias_target : Path.t option;
  values : (string * value ref) list;
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
}

type signature_origin = {
  named : Typedtree.module_type_declaration;
  annotations : Annotation.t list;
}

let rec direct_body (expression : Typedtree.module_expr) =
  match expression.mod_desc with
  | Tmod_structure body -> Some body
  | Tmod_constraint (body, _, _, _) -> direct_body body
  | _ -> None

let empty_signature =
  {
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
    types = [];
    modules = [];
    modtypes = [];
  }

let bind bindings name value =
  (name, value) :: List.Assoc.remove bindings name ~equal:String.equal

let member bindings name = List.Assoc.find bindings name ~equal:String.equal

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
  let all_types = ref [] in
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
            if imported normalized then
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
          | _ -> None)
    in
    let annotations = annotations_in declaration_scope children annotations in
    let* () =
      if imported then Ok ()
      else
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
                let value = { declaration; site; substitution = Subst.identity } in
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
            | Tsig_open _ -> unavailable item.sig_loc "An open in a module signature"
            | Tsig_include _ ->
                unavailable item.sig_loc "An include in a module signature"
            | Tsig_recmodule _ -> unavailable item.sig_loc "Recursive signature modules"
            | Tsig_typesubst _ | Tsig_modsubst _ | Tsig_modtypesubst _ ->
                unavailable item.sig_loc "A substitution in a module signature"
            | Tsig_typext _ | Tsig_exception _ | Tsig_class _ | Tsig_class_type _ ->
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
              } ))
      |> Result.all
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
      { empty_signature with signature_resources; signature_ghost_modules }
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
  let* () =
    List.fold_result source.libraries ~init:() ~f:(fun () library ->
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
            Ok ())
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
  let substitutions ~at substitution signature view =
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
              Ok
                (match (nested.signature_id, view.identity) with
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
  let rec constrain ~restricts_visibility ~boundary ~result_owner at substitution
      signature view =
    if Option.is_some view.checked then
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
      let* substitution = substitutions ~at substitution signature view in
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
                    substitution;
                    site = { signature_value.site with environment };
                  }
                in
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
                      constrain ~restricts_visibility ~boundary ~result_owner at
                        substitution signature.signature_body view
                    in
                    Ok (name, view)
                end)
        |> Result.all
      in
      Ok
        {
          view with
          values;
          types;
          modules = nested_modules;
          modtypes = signature.signature_modtypes;
        }
  in
  let apply_signature ~restricts_visibility ~result_owner at signature view =
    constrain ~restricts_visibility ~boundary:result_owner ~result_owner at Subst.identity
      signature view
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
  let rec module_expression annotations namespace ~identity
      (expression : Typedtree.module_expr) =
    match expression.mod_desc with
    | Tmod_structure structure ->
        collect_structure annotations namespace ~identity (scope expression.mod_loc)
          structure
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
          let* actual = module_expression annotations namespace ~identity body in
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
              let* actual_path =
                match actual.identity with
                | Some path -> Ok path
                | None ->
                    unavailable expression.mod_loc
                      "A checked module without a static path"
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
              let binding =
                ref
                  {
                    actual_path;
                    parameter_substitution = !parameter_substitution;
                    expected;
                    site;
                    namespace;
                    paths = [];
                  }
              in
              bindings := binding :: !bindings;
              Ok
                {
                  empty_module with
                  checked = Some binding;
                  identity = actual.identity;
                  application_identity = identity;
                }
          end
        else
          let* view = module_expression annotations namespace ~identity body in
          begin match annotation with
          | Tmodtype_explicit mty ->
              let* signature = signature_type ~imported:false annotations mty in
              let* view =
                apply_signature ~restricts_visibility:true ~result_owner:identity
                  mty.mty_loc signature view
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
                };
          }
    | Tmod_apply (callee, argument, _) ->
        specialize annotations namespace ~identity expression callee (Some argument)
    | Tmod_apply_unit callee ->
        specialize annotations namespace ~identity expression callee None
    | Tmod_unpack _ -> unavailable expression.mod_loc "A first-class module"
  and specialize annotations namespace ~identity (expression : Typedtree.module_expr)
      callee argument =
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
          module_expression annotations namespace ~identity:(Some stage_identity) callee
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
      module_expression definition.annotations namespace
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
            ( definition.template,
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
  and collect_structure annotations namespace ~identity declaration_scope
      (structure : Typedtree.structure) =
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
                              ref { declaration; namespace; paths = [ path; key ] }
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
                      module_expression all_annotations (namespace @ [ name ]) ~identity
                        declaration.mb_expr
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
            | Tstr_open _ -> unavailable item.str_loc "An open declaration"
            | Tstr_include _ -> unavailable item.str_loc "An include declaration"
            | Tstr_recmodule _ -> unavailable item.str_loc "Recursive module bindings"
            | Tstr_eval _ -> unavailable item.str_loc "A module initializer"
            | Tstr_primitive _ -> unavailable item.str_loc "An external value declaration"
            | Tstr_typext _ | Tstr_exception _ | Tstr_class _ | Tstr_class_type _ ->
                unavailable item.str_loc "This module structure item"
          in
          items view rest
    in
    items { empty_module with application_identity = identity } structure.str_items
  in
  let* view =
    collect_structure (Source.annotations source) [] ~identity:None source.scope structure
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
              apply_signature ~restricts_visibility:false ~result_owner:None
                interface.scope.location signature view
            in
            Ok ()
        end
  in
  Ok
    {
      structure =
        (let module_expr mapper expression =
           match List.Assoc.find !expansions expression ~equal:phys_equal with
           | Some body -> Tast_mapper.default.module_expr mapper body
           | None -> Tast_mapper.default.module_expr mapper expression
         in
         let map_structure mapper structure =
           let str_items =
             List.filter structure.Typedtree.str_items ~f:(fun item ->
                 match item.Typedtree.str_desc with
                 | Tstr_module { mb_id = Some id; _ } ->
                     not (List.mem !templates id ~equal:Ident.same)
                 | _ -> true)
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
      constraints = List.rev !constraints;
      specializations =
        List.rev_map !specializations
          ~f:(fun
              ( template,
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
