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

type signature_module = {
  signature_id : Ident.t option;
  signature_body : signature_view;
  signature_alias : Path.t option;
}

and signature_view = {
  signature_resources : (string * signature_resource) list;
  signature_values : (string * signature_value) list;
  signature_types : (string * Typedtree.type_declaration) list;
  signature_modules : (string * signature_module) list;
  signature_modtypes : (string * signature_view) list;
}

type checked_binding = {
  actual_path : Path.t;
  expected : signature_view;
  site : site;
  namespace : string list;
  paths : Path.t list;
}

type t = {
  values : value list;
  types : type_definition list;
  aliases : (Path.t * Path.t) list;
  bindings : checked_binding list;
}

type module_view = {
  checked : checked_binding ref option;
  identity : Path.t option;
  alias_target : Path.t option;
  values : (string * value ref) list;
  types : (string * type_definition ref) list;
  modules : (string * module_view) list;
  modtypes : (string * signature_view) list;
}

type signature_origin = {
  named : Typedtree.module_type_declaration;
  annotations : Annotation.t list;
}

let empty_signature =
  {
    signature_resources = [];
    signature_values = [];
    signature_types = [];
    signature_modules = [];
    signature_modtypes = [];
  }

let empty_module =
  {
    checked = None;
    identity = None;
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

let within (outer : Location.t) (inner : Location.t) =
  inner.loc_start.pos_cnum >= outer.loc_start.pos_cnum
  && inner.loc_end.pos_cnum <= outer.loc_end.pos_cnum

let annotations_in scope children annotations =
  List.filter annotations ~f:(fun (annotation : Annotation.t) ->
      within scope.Declaration_scope.location annotation.loc
      && not (List.exists children ~f:(fun child -> within child annotation.loc)))

let scope location : Declaration_scope.t = { location }

let build (source : Source.t) (structure : Typedtree.structure) :
    (t, Report.error) Result.t =
  let all_values = ref [] in
  let all_types = ref [] in
  let aliases = ref [] in
  let bindings = ref [] in
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
  let rec publish path view =
    register modules path view;
    Option.iter view.checked ~f:(fun binding ->
        binding := { !binding with paths = add_path !binding.paths path });
    if Option.is_none view.checked then
      Option.iter view.alias_target ~f:(fun target -> register aliases path target);
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
                    Ok { empty_module with identity = Some normalized }
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
            | Predicate -> Ok ()
            | Loop when Annotation.invariant_declaration annotation -> Ok ()
            | Loop | Ghost | Scope | Returns | Proof | Manual | Linearization | Initially
            | Initializes | Trusted ->
                if shared then Ok ()
                else
                  unavailable annotation.loc
                    "A declaration annotation in a nested module signature")
    in
    let rec items view = function
      | [] -> Ok view
      | (item : Typedtree.signature_item) :: rest ->
          let environment, next =
            match rest with
            | next :: _ -> (next.sig_env, Some next.sig_loc)
            | [] -> (signature.sig_final_env, None)
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
                                  within declaration.md_loc annotation.Annotation.loc)
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
          items view rest
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
    items { empty_signature with signature_resources } signature.sig_items
  in
  let rec signature_aliases substitution path signature =
    let substitution =
      List.fold signature.signature_modules ~init:substitution
        ~f:(fun substitution (name, nested) ->
          Option.value_map nested.signature_id ~default:substitution ~f:(fun id ->
              Subst.add_module id (Path.Pdot (path, name)) substitution))
    in
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
  let substitutions substitution signature view =
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
    List.fold_result signature.signature_modules ~init:substitution
      ~f:(fun substitution (name, nested) ->
        match member view.modules name with
        | None -> missing source.scope.location name
        | Some view ->
            Ok
              (match (nested.signature_id, view.identity) with
              | Some id, Some path -> Subst.add_module id path substitution
              | _ -> substitution))
  in
  let rec constrain substitution signature view =
    if Option.is_some view.checked then
      begin match (signature.signature_resources, signature.signature_values) with
      | (_, resource) :: _, _ ->
          unavailable resource.site.item_loc
            "A resource-bearing interface constraint on a checked module view"
      | [], (_, value) :: _ ->
          unavailable value.site.item_loc
            "An additional interface contract on a checked module view"
      | [], [] -> Ok view
      end
    else
      let* substitution = substitutions substitution signature view in
      let* values =
        List.map signature.signature_values ~f:(fun (name, signature_value) ->
            match member view.values name with
            | None -> missing signature_value.site.item_loc name
            | Some value ->
                let signature_value = { signature_value with substitution } in
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
            | None -> missing source.scope.location name
            | Some view ->
                begin match signature.signature_alias with
                | Some _ -> Ok (name, view)
                | None ->
                    let* view = constrain substitution signature.signature_body view in
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
  let apply_signature signature view = constrain Subst.identity signature view in
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
        Ok { result with identity = view.identity; checked = view.checked }
    | Mty_alias path -> resolve_module at env path
    | Mty_functor _ -> unavailable at "A functor signature"
    | Mty_ident _ -> unavailable at "An abstract module signature"
  in
  let rec module_expression annotations namespace (expression : Typedtree.module_expr) =
    match expression.mod_desc with
    | Tmod_structure structure ->
        collect_structure annotations namespace (scope expression.mod_loc) structure
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
          let* actual = module_expression annotations namespace body in
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
              let binding = ref { actual_path; expected; site; namespace; paths = [] } in
              bindings := binding :: !bindings;
              Ok { empty_module with checked = Some binding; identity = actual.identity }
          end
        else
          let* view = module_expression annotations namespace body in
          begin match annotation with
          | Tmodtype_explicit mty ->
              let* signature = signature_type ~imported:false annotations mty in
              let* () =
                if List.is_empty signature.signature_resources then Ok ()
                else
                  unavailable mty.mty_loc
                    "A resource declaration on an inline module structure"
              in
              apply_signature signature view
          | Tmodtype_implicit -> effective expression.mod_env expression.mod_loc mty view
          end
    | Tmod_functor _ -> unavailable expression.mod_loc "A functor"
    | Tmod_apply _ | Tmod_apply_unit _ ->
        unavailable expression.mod_loc "A functor application"
    | Tmod_unpack _ -> unavailable expression.mod_loc "A first-class module"
  and collect_structure annotations namespace declaration_scope
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
                              within binding.Typedtree.vb_expr.exp_loc annotation.loc)
                      | _ -> false)
                    || attached rest
              in
              if attached structure.str_items then Ok ()
              else
                Error
                  (Report.error Type annotation.loc
                     "This contract is outside a function declaration")
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
                      let definition =
                        ref
                          {
                            declaration;
                            namespace;
                            paths = [ Path.Pident declaration.typ_id ];
                          }
                      in
                      all_types := definition :: !all_types;
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
                      module_expression all_annotations (namespace @ [ name ])
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
    items empty_module structure.str_items
  in
  let* view =
    collect_structure (Annotation.of_comments source.comments) [] source.scope structure
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
            let* _ = apply_signature signature view in
            Ok ()
        end
  in
  Ok
    {
      values = List.rev_map !all_values ~f:(fun value -> !value);
      types = List.rev_map !all_types ~f:(fun definition -> !definition);
      aliases = List.rev !aliases;
      bindings = List.rev_map !bindings ~f:(fun binding -> !binding);
    }
