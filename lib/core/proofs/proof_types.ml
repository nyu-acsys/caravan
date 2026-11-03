(** The typing of a source's proofs: their types and constructors, elaborated into the
    compiler's environment, the proof modules of its scopes and signatures, and the proof
    resources its libraries import. *)

open Base
open Source_core

let rec monotype typ =
  match Types.get_desc typ with Tpoly (body, []) -> monotype body | _ -> typ

let rec function_arguments typ =
  let typ = monotype typ in
  match Types.get_desc typ with
  | Tarrow (_, argument, rest, _) ->
      let arguments, result = function_arguments rest in
      (monotype argument :: arguments, result)
  | _ -> ([], typ)

let interface_type_declarations = function
  | None -> []
  | Some (interface : interface) ->
      List.concat_map interface.signature ~f:(fun item ->
          match item.psig_desc with
          | Psig_type (_, declarations) | Psig_typesubst declarations -> declarations
          | _ -> [])

let interface_constructors = function
  | None -> []
  | Some (interface : interface) ->
      List.concat_map interface.signature ~f:(fun item ->
          match item.psig_desc with
          | Psig_type (_, declarations) | Psig_typesubst declarations ->
              List.concat_map declarations ~f:(fun declaration ->
                  match declaration.ptype_kind with
                  | Ptype_variant constructors ->
                      List.map constructors ~f:(fun c -> c.pcd_name.txt)
                  | _ -> [])
          | Psig_typext extension ->
              List.map extension.ptyext_constructors ~f:(fun c -> c.pext_name.txt)
          | _ -> [])

let proof_type_collision ?(allow_shadowing = false) env interface proof =
  let declared =
    List.map (interface_type_declarations interface) ~f:(fun d -> d.ptype_name.txt)
  in
  let rec find seen = function
    | [] -> None
    | S.Proof_type { type_name; _ } :: rest ->
        if
          List.mem seen type_name.pid_str ~equal:String.equal
          || List.mem declared type_name.pid_str ~equal:String.equal
          || (not allow_shadowing)
             && Option.is_some (find_type_by_name env type_name.pid_str)
        then Some type_name
        else find (type_name.pid_str :: seen) rest
    | _ :: rest -> find seen rest
  in
  find [] proof

let proof_constructor_collision ?(allow_shadowing = false) env interface proof =
  let declared = interface_constructors interface in
  let constructors =
    List.concat_map proof ~f:(function
      | S.Proof_type { type_kind = Variant ctors; _ } -> List.map ctors ~f:fst
      | _ -> [])
  in
  let rec find seen = function
    | [] -> None
    | (name : S.id) :: rest ->
        if
          List.mem seen name.pid_str ~equal:String.equal
          || List.mem declared name.pid_str ~equal:String.equal
          || (not allow_shadowing)
             && Option.is_some (find_constructor_by_name env name.pid_str)
        then Some name
        else find (name.pid_str :: seen) rest
  in
  find [] constructors

(** Type-checks the algebraic types of [proof] in [env], after the implementation, and
    returns their descriptors and the environment for the rest of the proof. *)
let elaborate_proof_types ?(add_standard = true) ?(allow_interfaces = false)
    ?(allow_shadowing = false) ?(previous = ([], [], [], [])) ?complete_proof
    ?(canonical_owner = Fn.id) (env : Env.t) (interface : interface option)
    (proof : S.proof_decl list) :
    ( Env.t * Datatypes.t list * proof_resource list * proof_field list * proof_au list,
      Report.error )
    Result.t =
  let complete_proof = Option.value complete_proof ~default:proof in
  let* () =
    match proof_type_collision ~allow_shadowing env interface proof with
    | None -> Ok ()
    | Some name ->
        Error
          (Report.error Type name.pid_loc
             (Printf.sprintf "The proof type %s is already declared" name.pid_str))
  in
  let* () =
    match proof_constructor_collision ~allow_shadowing env interface proof with
    | None -> Ok ()
    | Some name ->
        Error
          (Report.error Type name.pid_loc
             (Printf.sprintf "The proof constructor %s is already declared" name.pid_str))
  in
  let checked_constructor env ~at ~name parameters body =
    let declaration =
      Ast_helper.Type.mk ~loc:at
        ~params:
          (List.map parameters ~f:(fun parameter ->
               ( Ast_helper.Typ.var ~loc:parameter.S.pid_loc parameter.pid_str,
                 (Asttypes.NoVariance, Asttypes.NoInjectivity) )))
        ~manifest:(core_type ~at body)
        { txt = Compiler_types.internal_name ~at ("argument_" ^ name); loc = at }
    in
    let typed =
      Typemod.type_interface env [ Ast_helper.Sig.type_ Nonrecursive [ declaration ] ]
    in
    match typed.sig_type with
    | [ Types.Sig_type (_, declaration, _, _) ] ->
        (declaration.type_params, Option.value_exn declaration.type_manifest)
    | _ -> failwith "A type argument must elaborate to one type declaration"
  in
  let apply_parameters parameters arguments typ =
    Option.value_exn (Datatypes.instantiate_alias parameters arguments typ)
  in
  let module_exists env name =
    try
      let _ = Env.find_module_by_name (Lident name) env in
      true
    with Stdlib.Not_found -> false
  in
  let value_exists env name =
    try
      let _ = Env.find_value_by_name (Lident name) env in
      true
    with Stdlib.Not_found -> false
  in
  let signature env signature = (Typemod.type_interface env signature).sig_final_env in
  let value env (name : S.id) typ =
    if (not allow_shadowing) && value_exists env name.pid_str then
      Error
        (Report.error Type name.pid_loc
           (Printf.sprintf "The proof value %s is already declared" name.pid_str))
    else
      Ok
        (signature env
           [
             Ast_helper.Sig.value
               (Ast_helper.Val.mk ~loc:name.pid_loc
                  { txt = name.pid_str; loc = name.pid_loc }
                  typ);
           ])
  in
  let reserve_module env name =
    try
      let _, declaration = Env.find_module_by_name (Lident name) env in
      Error
        (Report.error Type declaration.md_loc
           (Printf.sprintf "The module %s is reserved for specifications" name))
    with Stdlib.Not_found -> Ok ()
  in
  let* env =
    if not add_standard then Ok env
    else
      let* () = reserve_module env "Ghost" in
      let* () = reserve_module env "Permission" in
      let env =
        signature env
          (Parse.interface
             (Lexing.from_string
                "module Ghost : sig type t type ('owner, 'value) field end"))
      in
      Ok
        (signature env
           (Parse.interface
              (Lexing.from_string
                 "module Permission : sig type t val half : t val full : t end")))
  in
  let previous_types, previous_resources, previous_fields, previous_aus = previous in
  let resource_at_path env resources path =
    let private_id =
      List.find resources ~f:(fun resource ->
          Path.same path (Pident resource.resource_id))
    in
    let private_representation =
      try
        let declaration = Env.find_type (Path.Pdot (path, "t")) env in
        Option.is_some declaration.type_manifest
      with Stdlib.Not_found -> false
    in
    let public_view =
      if private_representation then None
      else
        List.find_map resources ~f:(fun resource ->
            Option.bind resource.resource_public ~f:(fun public ->
                Option.some_if (resource_has_path public path) public))
    in
    let private_path =
      List.find resources ~f:(fun resource -> resource_has_path resource path)
    in
    Option.first_some private_id (Option.first_some public_view private_path)
  in
  let aus = ref (List.rev previous_aus) in
  let* env, reversed, resources, fields =
    List.fold_result proof
      ~init:
        ( env,
          List.rev previous_types,
          List.rev previous_resources,
          List.rev previous_fields )
      ~f:(fun (env, descriptors, resources, fields) declaration ->
        match declaration with
        | S.Proof_type { type_name; type_params; type_kind } ->
            let constructor ((name : S.id), (args : S.pty list)) =
              Ast_helper.Type.constructor ~loc:name.pid_loc
                ~args:(Pcstr_tuple (List.map args ~f:(core_type ~at:name.pid_loc)))
                { txt = name.pid_str; loc = name.pid_loc }
            in
            let label ((name : S.id), (ty : S.pty)) =
              Ast_helper.Type.field ~loc:name.pid_loc
                { txt = name.pid_str; loc = name.pid_loc }
                (core_type ~at:name.pid_loc ty)
            in
            let kind =
              match type_kind with
              | Variant ctors -> Parsetree.Ptype_variant (List.map ctors ~f:constructor)
              | Record fields -> Ptype_record (List.map fields ~f:label)
            in
            let declaration =
              let params =
                List.map type_params ~f:(fun parameter ->
                    ( Ast_helper.Typ.var ~loc:parameter.pid_loc parameter.pid_str,
                      (Asttypes.NoVariance, Asttypes.NoInjectivity) ))
              in
              Ast_helper.Type.mk ~loc:type_name.pid_loc ~kind ~params
                { txt = type_name.pid_str; loc = type_name.pid_loc }
            in
            let typed, _, _, _, env =
              Typemod.type_structure env
                [ Ast_helper.Str.type_ Recursive [ declaration ] ]
            in
            let typed_declarations =
              List.concat_map typed.str_items ~f:(fun item ->
                  match item.str_desc with Tstr_type (_, ds) -> ds | _ -> [])
            in
            let* added =
              Result.all
                (List.map typed_declarations ~f:(fun declaration ->
                     Result.map
                       (Datatypes.of_declaration declaration)
                       ~f:Datatypes.with_mathematical_domain))
            in
            Ok (env, List.rev_append added descriptors, resources, fields)
        | Proof_au { au_name = name; au_operation = operation } ->
            let at = name.pid_loc in
            let* () =
              if module_exists env name.pid_str then
                Error
                  (Report.error Type at
                     (Printf.sprintf "The proof module %s is already declared"
                        name.pid_str))
              else Ok ()
            in
            let* operation_path, operation_type =
              try
                let path, value = Env.find_value_by_name (longident operation) env in
                Ok
                  ( Env.normalize_value_path (Some at) env path |> canonical_owner,
                    value.Types.val_type )
              with Stdlib.Not_found ->
                Error
                  (Report.error Type (S.qualid_loc operation)
                     "The AU operation is not an OCaml function")
            in
            let args, result = function_arguments operation_type in
            let* () =
              if List.is_empty args then
                Error (Report.error Type at "The AU operation must be a function")
              else Ok ()
            in
            let* scheme = Polymorphic_functions.discover ~at operation_type in
            let parameters = scheme.variables in
            let declaration =
              let params =
                List.mapi parameters ~f:(fun index _ ->
                    ( Ast_helper.Typ.var ~loc:at ("a" ^ Int.to_string index),
                      (Asttypes.NoVariance, Asttypes.NoInjectivity) ))
              in
              Ast_helper.Sig.module_
                (Ast_helper.Md.mk ~loc:at
                   { txt = Some name.pid_str; loc = at }
                   (Ast_helper.Mty.signature ~loc:at
                      [
                        Ast_helper.Sig.type_ Nonrecursive
                          [
                            Ast_helper.Type.mk ~loc:at ~params { txt = "token"; loc = at };
                          ];
                      ]))
            in
            let typed = Typemod.type_interface env [ declaration ] in
            let env = typed.sig_final_env in
            let module_path, module_declaration =
              Env.find_module_by_name (Lident name.pid_str) env
            in
            let* module_id, module_signature =
              match (module_path, module_declaration.md_type) with
              | Pident id, Mty_signature items -> Ok (id, items)
              | _ -> Error (Report.error Type at "An AU must be a local module")
            in
            let token_path, _ =
              Env.find_type_by_name
                (Ldot
                   ({ txt = Lident name.pid_str; loc = at }, { txt = "token"; loc = at }))
                env
            in
            let token =
              Btype.newgenty (Types.get_desc (Ctype.newconstr token_path parameters))
            in
            let arrow args result =
              List.fold_right args ~init:result ~f:(fun arg result ->
                  let arg =
                    match Types.get_desc arg with
                    | Tpoly _ -> arg
                    | _ -> Btype.newgenty (Tpoly (arg, []))
                  in
                  Btype.newgenty (Tarrow (Nolabel, arg, result, Types.commu_ok)))
            in
            let value (name, args, result) =
              let id = Ident.create_local name in
              Types.Sig_value
                ( id,
                  {
                    val_type = Compiler_types.scheme_structure (arrow args result);
                    val_kind = Val_reg;
                    val_loc = at;
                    val_attributes = [];
                    val_uid = Shape.Uid.internal_not_actually_unique;
                  },
                  Exported )
            in
            let values =
              [
                ("bind", [ Predef.type_unit ], token);
                ("pending", token :: args, Predef.type_bool);
                ("committed", token :: (args @ [ result ]), Predef.type_bool);
                ("abort", token :: args, Predef.type_unit);
                ("commit", token :: (args @ [ result ]), Predef.type_unit);
              ]
            in
            let env =
              Env.add_module module_id Mp_present
                (Mty_signature (module_signature @ List.map values ~f:value))
                env
            in
            aus :=
              {
                au_name = name.pid_str;
                au_scope = None;
                au_id = module_id;
                au_path = module_path;
                au_environment = env;
                au_operation = operation;
                au_operation_path = operation_path;
                au_operation_type = operation_type;
                au_parameters = parameters;
                au_token = token;
                au_token_path = token_path;
                au_token_paths = [ token_path ];
                au_at = at;
                au_application = None;
              }
              :: !aus;
            Ok (env, descriptors, resources, fields)
        | Proof_resource { resource_name = name; resource_functor; resource_arguments } ->
            let at = name.pid_loc in
            let bound_module =
              try
                let path, _ = Env.find_module_by_name (longident resource_functor) env in
                let path = Env.normalize_module_path None env path |> canonical_owner in
                resource_at_path env resources path
              with Stdlib.Not_found -> None
            in
            let* () =
              if Option.is_some bound_module && not (List.is_empty resource_arguments)
              then
                Error
                  (Report.error Type
                     (S.qualid_loc resource_functor)
                     ("The proof module "
                     ^ String.concat ~sep:"."
                         (Proof_library.path_of_qualid resource_functor)
                     ^ " is not a functor"))
              else Ok ()
            in
            let alias_target =
              if List.is_empty resource_arguments then bound_module else None
            in
            begin match alias_target with
            | Some target ->
                let* () =
                  if module_exists env name.pid_str then
                    Error
                      (Report.error Type at
                         (Printf.sprintf "The proof module %s is already declared"
                            name.pid_str))
                  else Ok ()
                in
                let alias =
                  Ast_helper.Str.module_
                    (Ast_helper.Mb.mk ~loc:at
                       { txt = Some name.pid_str; loc = at }
                       (Ast_helper.Mod.ident ~loc:at
                          { txt = longident resource_functor; loc = at }))
                in
                let _, _, _, _, env = Typemod.type_structure env [ alias ] in
                let path, _ = Env.find_module_by_name (Lident name.pid_str) env in
                let* resource_id =
                  match path with
                  | Pident id -> Ok id
                  | _ -> Error (Report.error Type at "A proof alias must be local")
                in
                let descriptor =
                  {
                    (Datatypes.resource_type ~name:name.pid_str ~module_id:resource_id ~at)
                    with
                    alias = Some target.resource_type;
                    parameters = target.resource_parameters;
                  }
                in
                let aliases =
                  List.map target.resource_aliases ~f:(fun previous ->
                      let member =
                        match previous.Datatypes.library with
                        | Some (Pdot (_, member)) -> member
                        | _ -> "element"
                      in
                      {
                        (Datatypes.library_type ~library:name.pid_str
                           ~library_id:resource_id ~at member)
                        with
                        alias = previous.alias;
                        parameters = previous.parameters;
                      })
                in
                let resource =
                  {
                    target with
                    resource_name = name.pid_str;
                    resource_backend = name.pid_str;
                    resource_scope = None;
                    resource_path = Pident resource_id;
                    resource_environment = env;
                    resource_arguments = [];
                    resource_alias_of = Some target.resource_path;
                    resource_definition = false;
                    resource_abstract = false;
                    resource_representation = None;
                    resource_id;
                    resource_descriptor = descriptor;
                    resource_aliases = aliases;
                    resource_at = at;
                    resource_public = None;
                    resource_application = None;
                  }
                in
                Ok (env, descriptors, resource :: resources, fields)
            | None ->
                let* signatures = Proof_library.signatures at in
                let functor_path = Proof_library.path_of_qualid resource_functor in
                let* library =
                  match Proof_library.find signatures functor_path with
                  | Some library when allow_interfaces || not library.interface ->
                      Ok library
                  | Some _ ->
                      Error
                        (Report.error Type at "A proof module must name a library module")
                  | None ->
                      Error
                        (Report.error Type
                           (S.qualid_loc resource_functor)
                           ("Unknown Raven library module "
                           ^ String.concat ~sep:"." functor_path))
                in
                let library_types = Proof_library.member_types signatures library in
                let library_constants =
                  Proof_library.member_constants signatures library
                in
                let ra_interface =
                  if Proof_library.is_resource_algebra signatures library then
                    Proof_library.find signatures [ "ResourceAlgebra" ]
                  else None
                in
                let* () =
                  if
                    module_exists env name.pid_str
                    || Option.is_some
                         (find_type_by_name env (String.uncapitalize name.pid_str))
                    || List.exists complete_proof ~f:(function
                      | S.Proof_type { type_name; _ } ->
                          String.equal (String.capitalize type_name.pid_str) name.pid_str
                      | _ -> false)
                    || List.mem
                         [ "Ghost"; "Permission"; "Finset" ]
                         name.pid_str ~equal:String.equal
                  then
                    Error
                      (Report.error Type at
                         (Printf.sprintf
                            "The proof module %s is already declared or reserved"
                            name.pid_str))
                  else Ok ()
                in
                let* () =
                  if List.length library.parameters = List.length resource_arguments then
                    Ok ()
                  else
                    Error
                      (Report.error Type at
                         (Printf.sprintf "%s expects %d module argument(s)"
                            (String.concat ~sep:"." functor_path)
                            (List.length library.parameters)))
                in
                let pairs = List.zip_exn library.parameters resource_arguments in
                let* arguments =
                  Result.all
                    (List.map pairs ~f:(fun (parameter, argument) ->
                         match argument with
                         | S.Proof_type_argument { type_params; type_body } ->
                             let* () =
                               if
                                 Proof_library.accepts_type_argument signatures
                                   parameter.interface
                               then Ok ()
                               else
                                 Error
                                   (Report.error Type at
                                      (Printf.sprintf "Parameter %s requires a module"
                                         parameter.name))
                             in
                             let parameters, body =
                               checked_constructor env ~at ~name:parameter.name
                                 type_params type_body
                             in
                             Ok (Type_argument body, parameters)
                         | Proof_module_argument module_name ->
                             let loc = S.qualid_loc module_name in
                             let* path =
                               try
                                 let path, _ =
                                   Env.find_module_by_name (longident module_name) env
                                 in
                                 Ok
                                   (Env.normalize_module_path None env path
                                   |> canonical_owner)
                               with Stdlib.Not_found ->
                                 Error
                                   (Report.error Type loc
                                      "The proof module argument is not declared")
                             in
                             let* actual =
                               match resource_at_path env resources path with
                               | Some resource -> Ok resource
                               | None ->
                                   Error
                                     (Report.error Type loc
                                        "The proof module argument must be declared \
                                         earlier")
                             in
                             let acceptable =
                               List.equal String.equal actual.resource_functor
                                 parameter.interface
                               || List.exists actual.resource_interfaces
                                    ~f:(fun interface ->
                                      List.equal String.equal interface
                                        parameter.interface)
                             in
                             let* () =
                               if acceptable then Ok ()
                               else
                                 Error
                                   (Report.error Type loc
                                      (Printf.sprintf
                                         "The proof module argument does not implement %s"
                                         (String.concat ~sep:"." parameter.interface)))
                             in
                             Ok (Module_argument path, actual.resource_parameters)))
                in
                let arities =
                  List.filter_map arguments ~f:(fun (_, parameters) ->
                      Option.some_if
                        (not (List.is_empty parameters))
                        (List.length parameters))
                in
                let arity = Option.value (List.hd arities) ~default:0 in
                let* () =
                  if List.for_all arities ~f:(Int.equal arity) then Ok ()
                  else
                    Error
                      (Report.error Type at
                         "A proof module family requires equal nonzero argument arities")
                in
                let family_names = List.init arity ~f:(fun i -> "a" ^ Int.to_string i) in
                let resource_parameters =
                  List.map family_names ~f:(fun name ->
                      Btype.newgenty (Types.Tvar (Some name)))
                in
                let family_arguments =
                  List.map family_names ~f:(Ast_helper.Typ.var ~loc:at)
                in
                let family_type_params =
                  List.map family_arguments ~f:(fun typ ->
                      (typ, (Asttypes.NoVariance, Asttypes.NoInjectivity)))
                in
                let arguments =
                  List.map arguments ~f:(fun (argument, parameters) ->
                      match argument with
                      | Type_argument typ ->
                          let arguments =
                            if List.is_empty parameters then [] else resource_parameters
                          in
                          Type_argument (apply_parameters parameters arguments typ)
                      | Module_argument _ -> argument)
                in
                let rec same_resource left right =
                  if Ident.same left.resource_id right.resource_id then true
                  else
                    match (left.resource_alias_of, right.resource_alias_of) with
                    | Some path, _ ->
                        Option.exists (resource_at_path env resources path)
                          ~f:(fun target -> same_resource target right)
                    | _, Some path ->
                        Option.exists (resource_at_path env resources path)
                          ~f:(fun target -> same_resource left target)
                    | None, None ->
                        begin match
                          (left.resource_application, right.resource_application)
                        with
                        | Some (left_app, left_template), Some (right_app, right_template)
                          ->
                            Path.same left_app right_app
                            && Ident.same left_template right_template
                        | Some _, None | None, Some _ -> false
                        | None, None ->
                            (not left.resource_definition)
                            && (not right.resource_definition)
                            && (not left.resource_abstract)
                            && (not right.resource_abstract)
                            && List.equal String.equal left.resource_functor
                                 right.resource_functor
                            && same_arguments left.resource_parameters
                                 right.resource_parameters left.resource_arguments
                                 right.resource_arguments
                        end
                and same_arguments left_parameters right_parameters left right =
                  List.length left = List.length right
                  && List.length left_parameters = List.length right_parameters
                  && List.for_all2_exn left right ~f:(fun left right ->
                      match (left, right) with
                      | Type_argument _, Type_argument _ -> true
                      | Module_argument left, Module_argument right ->
                          if Path.same left right then true
                          else
                            begin match
                              ( resource_at_path env resources left,
                                resource_at_path env resources right )
                            with
                            | Some left, Some right -> same_resource left right
                            | _ -> false
                            end
                      | Type_argument _, Module_argument _
                      | Module_argument _, Type_argument _ ->
                          false)
                  && Ctype.is_equal env true
                       (left_parameters
                       @ List.filter_map left ~f:(function
                         | Type_argument typ -> Some typ
                         | Module_argument _ -> None))
                       (right_parameters
                       @ List.filter_map right ~f:(function
                         | Type_argument typ -> Some typ
                         | Module_argument _ -> None))
                in
                let applicative_source =
                  List.find resources ~f:(fun resource ->
                      Option.is_none resource.resource_alias_of
                      && (not resource.resource_definition)
                      && (not resource.resource_abstract)
                      && List.equal String.equal resource.resource_functor library.path
                      && same_arguments resource.resource_parameters resource_parameters
                           resource.resource_arguments arguments)
                in
                let* env, type_members =
                  match applicative_source with
                  | Some previous ->
                      let env =
                        List.fold previous.resource_type_members ~init:env
                          ~f:(fun env (_, id, declaration) ->
                            match find_type_by_name env (Ident.name id) with
                            | Some _ -> env
                            | None -> Env.add_type ~check:false id declaration env)
                      in
                      Ok (env, previous.resource_type_members)
                  | None ->
                      let anchored =
                        List.filter library_types ~f:(fun member ->
                            member.rep || Option.is_none member.definition)
                      in
                      let hidden_name (member : Checked_signatures.type_member) =
                        Compiler_types.internal_name ~at member.name
                      in
                      let declarations =
                        List.map anchored ~f:(fun member ->
                            Ast_helper.Sig.type_ Nonrecursive
                              [
                                Ast_helper.Type.mk ~loc:at ~params:family_type_params
                                  { txt = hidden_name member; loc = at };
                              ])
                      in
                      let env = (Typemod.type_interface env declarations).sig_final_env in
                      let* members =
                        Result.all
                          (List.map anchored ~f:(fun member ->
                               match find_type_by_name env (hidden_name member) with
                               | Some (Pident id, declaration) ->
                                   Ok (member.name, id, declaration)
                               | _ ->
                                   Error
                                     (Report.error Type at
                                        "A proof type identity could not be created")))
                      in
                      Ok (env, members)
                in
                let alias_name (parameter : Checked_signatures.parameter) =
                  if List.length library.parameters = 1 then "element"
                  else String.uncapitalize parameter.Checked_signatures.name
                in
                let alias_names =
                  List.filter_map pairs ~f:(fun (parameter, argument) ->
                      match argument with
                      | S.Proof_type_argument { type_params; type_body } ->
                          let names =
                            if List.is_empty type_params then []
                            else
                              List.zip_exn
                                (List.map type_params ~f:(fun parameter ->
                                     parameter.S.pid_str))
                                family_names
                          in
                          let rec rename = function
                            | S.PTtyvar id ->
                                let name =
                                  List.Assoc.find_exn names id.pid_str ~equal:String.equal
                                in
                                S.PTtyvar { id with pid_str = name }
                            | PTtyapp (name, arguments) ->
                                S.PTtyapp (name, List.map arguments ~f:rename)
                            | PTtuple elements -> S.PTtuple (List.map elements ~f:rename)
                            | PTarrow (argument, result) ->
                                S.PTarrow (rename argument, rename result)
                          in
                          Some (parameter.name, alias_name parameter, rename type_body)
                      | Proof_module_argument _ -> None)
                in
                let named ?(arguments = []) name =
                  Ast_helper.Typ.constr ~loc:at { txt = Lident name; loc = at } arguments
                in
                let substitutions =
                  List.map (List.zip_exn pairs arguments)
                    ~f:(fun ((formal, argument), typed_argument) ->
                      let typ =
                        match argument with
                        | S.Proof_type_argument _ ->
                            named ~arguments:family_arguments (alias_name formal)
                        | Proof_module_argument q ->
                            let actual =
                              match typed_argument with
                              | Module_argument path ->
                                  Option.value_exn (resource_at_path env resources path)
                              | Type_argument _ ->
                                  failwith "A module argument must retain its kind"
                            in
                            Ast_helper.Typ.constr ~loc:at
                              {
                                txt =
                                  Ldot
                                    ( { txt = longident q; loc = at },
                                      { txt = "t"; loc = at } );
                                loc = at;
                              }
                              (if List.is_empty actual.resource_parameters then []
                               else family_arguments)
                      in
                      (formal.name, typ))
                in
                let metadata_type =
                  Proof_library.ocaml_type ~family_arguments ~at ~signature:library
                    ~substitutions
                in
                let operation_type =
                  Proof_library.operation_type ~family_arguments ~at ~signature:library
                    ~substitutions
                in
                let* type_items =
                  Result.all
                    (List.map library_types ~f:(fun member ->
                         let* manifest =
                           match
                             List.find type_members ~f:(fun (name, _, _) ->
                                 String.equal name member.name)
                           with
                           | Some (_, id, _) ->
                               Ok
                                 (Some (named ~arguments:family_arguments (Ident.name id)))
                           | None when Option.is_some member.definition && not member.rep
                             ->
                               let definition = Option.value_exn member.definition in
                               let* typ = metadata_type definition in
                               Ok (Some typ)
                           | _ -> Ok None
                         in
                         let declaration =
                           Ast_helper.Type.mk ~loc:at ~params:family_type_params ?manifest
                             { txt = String.uncapitalize member.name; loc = at }
                         in
                         Ok (Ast_helper.Sig.type_ Nonrecursive [ declaration ])))
                in
                let alias_items =
                  List.map alias_names ~f:(fun (_, alias, typ) ->
                      Ast_helper.Sig.type_ Nonrecursive
                        [
                          Ast_helper.Type.mk ~loc:at ~params:family_type_params
                            ~manifest:(core_type ~at typ) { txt = alias; loc = at };
                        ])
                in
                let operations = Proof_library.member_operations signatures library in
                let ra_operations =
                  Option.value_map ra_interface ~default:[] ~f:(fun selected ->
                      Proof_library.member_operations signatures selected)
                in
                let ra_constants =
                  Option.value_map ra_interface ~default:[] ~f:(fun selected ->
                      Proof_library.member_constants signatures selected)
                in
                let* operation_items =
                  Result.all
                    (List.map operations ~f:(fun operation ->
                         let* typ =
                           match
                             ( ra_interface,
                               List.find ra_operations ~f:(fun inherited ->
                                   String.equal inherited.name operation.name) )
                           with
                           | Some selected, Some inherited ->
                               Proof_library.operation_type ~family_arguments ~at
                                 ~signature:selected ~substitutions:[] inherited
                           | _ -> operation_type operation
                         in
                         Ok
                           (Ast_helper.Sig.value
                              (Ast_helper.Val.mk ~loc:at
                                 { txt = operation.name; loc = at }
                                 typ))))
                in
                let* constant_items =
                  Result.all
                    (List.map library_constants ~f:(fun (name, typ) ->
                         if
                           List.exists operations ~f:(fun operation ->
                               String.equal operation.name name)
                         then Ok None
                         else
                           let* typ =
                             match
                               ( ra_interface,
                                 List.Assoc.find ra_constants name ~equal:String.equal )
                             with
                             | Some selected, Some inherited ->
                                 Proof_library.ocaml_type ~family_arguments ~at
                                   ~signature:selected ~substitutions:[] inherited
                             | _ -> metadata_type typ
                           in
                           Ok
                             (Some
                                (Ast_helper.Sig.value
                                   (Ast_helper.Val.mk ~loc:at { txt = name; loc = at } typ)))))
                in
                let declaration =
                  Ast_helper.Sig.module_
                    (Ast_helper.Md.mk ~loc:at
                       { txt = Some name.pid_str; loc = at }
                       (Ast_helper.Mty.signature ~loc:at
                          (alias_items @ type_items @ operation_items
                          @ List.filter_opt constant_items)))
                in
                let typed = Typemod.type_interface env [ declaration ] in
                let env = typed.sig_final_env in
                let path, _ = Env.find_module_by_name (Lident name.pid_str) env in
                let* resource_id =
                  match path with
                  | Pident id -> Ok id
                  | _ -> Error (Report.error Type at "A proof module must be local")
                in
                let resource_type =
                  let path, _ =
                    Env.find_type_by_name
                      (Ldot
                         ({ txt = Lident name.pid_str; loc = at }, { txt = "t"; loc = at }))
                      env
                  in
                  Ctype.newconstr path resource_parameters
                in
                let resource_descriptor =
                  let descriptor =
                    Datatypes.resource_type ~name:name.pid_str ~module_id:resource_id ~at
                  in
                  let paths =
                    List.filter_map type_members ~f:(fun (member, id, _) ->
                        Option.some_if (String.equal member "T") (Path.Pident id))
                  in
                  let descriptor =
                    {
                      (Datatypes.with_paths descriptor paths) with
                      parameters = resource_parameters;
                    }
                  in
                  Option.value_map applicative_source ~default:descriptor
                    ~f:(fun previous ->
                      {
                        descriptor with
                        alias =
                          Some
                            (apply_parameters previous.resource_parameters
                               resource_parameters previous.resource_type);
                      })
                in
                let resource_aliases =
                  List.filter_map (List.zip_exn pairs arguments)
                    ~f:(fun ((formal, argument), typed_argument) ->
                      match (argument, typed_argument) with
                      | S.Proof_type_argument _, Type_argument typ ->
                          let alias = alias_name formal in
                          Some
                            {
                              (Datatypes.library_type ~library:name.pid_str
                                 ~library_id:resource_id ~at alias)
                              with
                              alias = Some typ;
                              parameters = resource_parameters;
                            }
                      | Proof_module_argument _, Module_argument _ -> None
                      | Proof_type_argument _, Module_argument _
                      | Proof_module_argument _, Type_argument _ ->
                          failwith "A resource argument must retain its kind")
                in
                let value_type operation =
                  let qualified =
                    Longident.Ldot
                      ( { txt = Longident.Lident name.pid_str; loc = at },
                        { txt = operation; loc = at } )
                  in
                  let _, value = Env.find_value_by_name qualified env in
                  let variables =
                    List.filter_map
                      (Polymorphic_functions.all_variables value.Types.val_type)
                      ~f:(fun variable ->
                        match Types.get_desc variable with
                        | Tvar (Some name) ->
                            Option.map
                              (List.findi family_names ~f:(fun _ family ->
                                   String.equal family name))
                              ~f:(fun (index, _) ->
                                (variable, List.nth_exn resource_parameters index))
                        | _ -> None)
                  in
                  let parameters, arguments = List.unzip variables in
                  let typ = apply_parameters parameters arguments value.Types.val_type in
                  let inputs, output = function_arguments typ in
                  (operation, inputs, output)
                in
                let resource_operations =
                  List.map operations ~f:(fun operation -> value_type operation.name)
                  @ List.filter_map library_constants ~f:(fun (constant, _) ->
                      Option.some_if
                        (not
                           (List.exists operations ~f:(fun operation ->
                                String.equal operation.name constant)))
                        (value_type constant))
                in
                let resource =
                  {
                    resource_name = name.pid_str;
                    resource_backend = name.pid_str;
                    resource_scope = None;
                    resource_path = Pident resource_id;
                    resource_environment = env;
                    resource_functor = library.path;
                    resource_arguments = arguments;
                    resource_parameters;
                    resource_is_ra = Proof_library.is_resource_algebra signatures library;
                    resource_interfaces = Proof_library.interface_paths signatures library;
                    resource_alias_of = None;
                    resource_definition = false;
                    resource_abstract = false;
                    resource_representation = None;
                    resource_type_members = type_members;
                    resource_type;
                    resource_id;
                    resource_operations;
                    resource_constants = List.map library_constants ~f:fst;
                    resource_descriptor;
                    resource_aliases;
                    resource_at = at;
                    resource_public = None;
                    resource_application = None;
                  }
                in
                Ok (env, descriptors, resource :: resources, fields)
            end
        | Proof_field { field_name = name; field_type } ->
            let at = name.pid_loc in
            let* () =
              match field_type with
              | PTtyapp (Qdot (Qid ghost, field), [ _; _ ])
                when String.equal ghost.pid_str "Ghost"
                     && String.equal field.pid_str "field" ->
                  Ok ()
              | _ ->
                  Error
                    (Report.error Type at
                       "A ghost field requires an (owner, value) Ghost.field type")
            in
            let* env = value env name (core_type ~at field_type) in
            let field_path, declaration =
              Env.find_value_by_name (Lident name.pid_str) env
            in
            let* owner, content =
              match Types.get_desc (monotype declaration.Types.val_type) with
              | Tconstr (_, [ owner; content ], _) -> Ok (owner, content)
              | _ ->
                  Error
                    (Report.error Type at "A ghost field must have two type parameters")
            in
            let field_parameters =
              Polymorphic_functions.all_variables declaration.val_type
              |> List.filter ~f:(fun typ -> Types.get_level typ = Btype.generic_level)
            in
            let owner_head = Ctype.expand_head env owner in
            let owner_is_reference =
              match Types.get_desc owner_head with
              | Tconstr (p, [ _ ], _) when Datatypes.is_atomic p || Datatypes.is_ref p ->
                  true
              | Tconstr (p, [], _) when Datatypes.is_ghost p -> true
              | Tconstr (p, _, _) ->
                  let declaration = Env.find_type p env in
                  begin match declaration.type_kind with
                  | Type_record (labels, _) ->
                      List.exists labels ~f:(fun label ->
                          match label.Types.ld_mutable with
                          | Mutable -> true
                          | Immutable -> false)
                  | _ -> false
                  end
              | _ -> false
            in
            let* () =
              if owner_is_reference then Ok ()
              else
                Error
                  (Report.error Type at "A ghost field owner must be a heap reference")
            in
            let field_resource =
              match Types.get_desc content with
              | Tconstr (Pdot (module_path, "t"), arguments, _) ->
                  let canonical =
                    Env.normalize_module_path None env module_path |> canonical_owner
                  in
                  Option.bind
                    (Option.first_some
                       (resource_at_path env resources module_path)
                       (resource_at_path env resources canonical))
                    ~f:(fun resource ->
                      Option.some_if
                        (resource.resource_is_ra
                        && List.length arguments
                           = List.length resource.resource_parameters)
                        (Path.Pident resource.resource_id))
              | _ -> None
            in
            let* field_id =
              match field_path with
              | Pident id -> Ok id
              | _ -> Error (Report.error Type at "A ghost field must be a local value")
            in
            Ok
              ( env,
                descriptors,
                resources,
                {
                  field_name = name.pid_str;
                  field_backend = name.pid_str;
                  field_scope = None;
                  field_id;
                  field_path;
                  field_environment = env;
                  field_owner = owner;
                  field_value = content;
                  field_parameters;
                  field_family = None;
                  field_resource;
                  field_at = at;
                }
                :: fields )
        | Proof_function { function_name = name; function_params; function_result; _ } ->
            let at = name.pid_loc in
            let typ =
              List.fold_right function_params ~init:(core_type ~at function_result)
                ~f:(fun (_, param) result ->
                  Ast_helper.Typ.arrow ~loc:at Nolabel (core_type ~at param) result)
            in
            let* env = value env name typ in
            Ok (env, descriptors, resources, fields)
        | _ -> Ok (env, descriptors, resources, fields))
  in
  Ok (env, List.rev reversed, List.rev resources, List.rev fields, List.rev !aus)

let signature_ghost_modules ~comments (scope : Proof_scopes.scope) =
  let within = Declaration_scope.contains in
  let parameter (parameter : Typedtree.functor_parameter) =
    match parameter with
    | Named
        ( Some parameter,
          _,
          ({ mty_desc = Tmty_ident (path, _); mty_env; mty_loc; _ } :
            Typedtree.module_type) ) ->
        let rec declared seen path =
          let path = Env.normalize_modtype_path mty_env path in
          if List.mem seen path ~equal:Path.same then
            Error (Report.error Type mty_loc "A cyclic module type alias")
          else
            let declaration = Env.find_modtype path mty_env in
            match declaration.mtd_type with
            | Some (Mty_ident next) -> declared (path :: seen) next
            | Some (Mty_signature _ | Mty_functor _ | Mty_alias _) | None ->
                Ok declaration
        in
        let* declaration = declared [] path in
        let nested =
          match declaration.mtd_type with
          | Some module_type ->
              begin match Mtype.scrape mty_env module_type with
              | Mty_signature members ->
                  List.filter_map members ~f:(function
                    | Types.Sig_module (_, _, declaration, _, _) ->
                        Some declaration.md_loc
                    | Sig_modtype (_, declaration, _) -> Some declaration.mtd_loc
                    | _ -> None)
              | Mty_ident _ | Mty_functor _ | Mty_alias _ -> []
              end
          | None -> []
        in
        let annotations =
          Annotation.of_comments comments
          |> List.filter ~f:(fun annotation ->
              Poly.equal (Annotation.kind annotation) Annotation.Ghost_module
              && within declaration.mtd_loc annotation.loc
              && not (List.exists nested ~f:(fun loc -> within loc annotation.loc)))
        in
        let* modules = Result.all (List.map annotations ~f:Annotation.ghost_module) in
        Ok (Some (parameter, modules))
    | Named _ | Unit -> Ok None
  in
  let* found = Result.all (List.map scope.parameters ~f:parameter) in
  Ok (List.filter_opt found)

let implicit_ghost_scopes ~comments (scopes : Proof_scopes.t) =
  let has_body (expression : Typedtree.module_expr) =
    let rec body expression =
      match expression.Typedtree.mod_desc with
      | Tmod_structure _ | Tmod_functor _ -> true
      | Tmod_constraint (inner, _, _, _) -> body inner
      | Tmod_ident _ | Tmod_apply _ | Tmod_apply_unit _ | Tmod_unpack _ -> false
    in
    body expression
  in
  let rec collect parent =
    List.fold_result parent.Proof_scopes.structure.str_items ~init:[]
      ~f:(fun found item ->
        match item.Typedtree.str_desc with
        | Tstr_module
            { mb_id = Some id; mb_name = { txt = Some name; loc }; mb_expr; mb_loc; _ }
          when has_body mb_expr ->
            let name = S.mk_id ~loc name in
            let* candidate =
              Proof_scopes.child_scope ~check_header:false parent name [] mb_loc
            in
            if not (Option.exists candidate.declaration_id ~f:(Ident.same id)) then
              Ok found
            else
              let existing =
                List.find scopes.scopes ~f:(fun scope ->
                    Option.exists scope.Proof_scopes.declaration_id ~f:(Ident.same id))
              in
              let current = Option.value existing ~default:candidate in
              let* abstract =
                match current.parameters with
                | _ :: _ ->
                    let* declared = signature_ghost_modules ~comments current in
                    Ok
                      (List.exists declared ~f:(fun (_, modules) ->
                           not (List.is_empty modules)))
                | [] -> Ok false
              in
              let found =
                if abstract && Option.is_none existing then found @ [ candidate ]
                else found
              in
              if List.is_empty current.parameters then
                let* nested = collect current in
                Ok (found @ nested)
              else Ok found
        | _ -> Ok found)
  in
  let* implicit = collect scopes.root in
  let ordered =
    List.stable_sort (scopes.scopes @ implicit) ~compare:(fun left right ->
        Int.compare left.source_location.loc_start.pos_cnum
          right.source_location.loc_start.pos_cnum)
  in
  Ok ({ scopes with scopes = ordered }, implicit)

let public_ghost_occurrences ?public_interface ~comments scopes
    (scope : Proof_scopes.scope) =
  let parent =
    Option.value_map scope.Proof_scopes.parent ~default:scopes.Proof_scopes.root.structure
      ~f:(fun path ->
        Option.value_map (Proof_scopes.find_owner scopes (Some path))
          ~default:scopes.root.structure ~f:(fun owner -> owner.structure))
  in
  let rec explicit_type (expression : Typedtree.module_expr) =
    match expression.mod_desc with
    | Tmod_constraint (_, _, Tmodtype_explicit typ, _) -> Some typ
    | Tmod_functor (_, body) | Tmod_constraint (body, _, Tmodtype_implicit, _) ->
        explicit_type body
    | Tmod_structure _ | Tmod_ident _ | Tmod_apply _ | Tmod_apply_unit _ | Tmod_unpack _
      ->
        None
  in
  let signature_location (typ : Typedtree.module_type) =
    match typ.mty_desc with
    | Tmty_ident (path, _) ->
        let declaration = Env.find_modtype path typ.mty_env in
        declaration.mtd_loc
    | Tmty_signature _ | Tmty_functor _ | Tmty_with _ | Tmty_typeof _ | Tmty_alias _ ->
        typ.mty_loc
  in
  let explicit =
    List.find_map parent.str_items ~f:(fun item ->
        match item.str_desc with
        | Tstr_module { mb_id = Some id; mb_expr; _ }
          when Option.exists scope.declaration_id ~f:(Ident.same id) ->
            explicit_type mb_expr
        | _ -> None)
  in
  let interface_type =
    match (scope.namespace, public_interface) with
    | [ name ], Some interface ->
        Option.bind interface.typed_signature ~f:(fun signature ->
            List.find_map signature.sig_items ~f:(fun item ->
                match item.sig_desc with
                | Tsig_module { md_id = Some id; md_type; _ }
                  when String.equal (Ident.name id) name ->
                    Some md_type
                | _ -> None))
    | _ -> None
  in
  match Option.first_some interface_type explicit with
  | None -> Ok []
  | Some typ ->
      let location = signature_location typ in
      let within = Declaration_scope.contains in
      let annotations = Annotation.of_comments comments in
      let rec collect names location signature =
        let children =
          List.filter_map signature ~f:(function
            | Types.Sig_module (id, _, declaration, _, _) ->
                Some (Some (Ident.name id), declaration.md_loc, declaration.md_type)
            | Sig_modtype (_, declaration, _) ->
                Some (None, declaration.mtd_loc, Types.Mty_signature [])
            | _ -> None)
        in
        let direct =
          List.filter annotations ~f:(fun annotation ->
              Poly.equal (Annotation.kind annotation) Annotation.Ghost_module
              && within location annotation.loc
              && not
                   (List.exists children ~f:(fun (_, child, _) ->
                        within child annotation.loc)))
        in
        let* direct = Result.all (List.map direct ~f:Annotation.ghost_module) in
        let* nested =
          List.filter_map children ~f:(function
            | Some name, child, module_type ->
                begin match Mtype.scrape typ.mty_env module_type with
                | Mty_signature body -> Some (collect (names @ [ name ]) child body)
                | Mty_ident _ | Mty_functor _ | Mty_alias _ -> None
                end
            | None, _, _ -> None)
          |> Result.all
        in
        Ok
          (List.map direct ~f:(fun declaration -> (names, declaration))
          @ List.concat nested)
      in
      begin match Mtype.scrape typ.mty_env typ.mty_type with
      | Mty_signature body -> collect [] location body
      | Mty_ident _ | Mty_functor _ | Mty_alias _ -> Ok []
      end

let public_ghost_modules ?public_interface ~comments scopes scope =
  let* occurrences = public_ghost_occurrences ?public_interface ~comments scopes scope in
  Ok
    (List.filter_map occurrences ~f:(function
      | [], declaration -> Some declaration
      | _ :: _, _ -> None))

let scoped_proof_types ?only ?only_ids ?public_interface ?(previous_resources = [])
    ~applications ~comments runtime_env root_env (scopes : Proof_scopes.t) =
  let applications =
    List.filter applications ~f:(fun (application : Functor_context.application) ->
        not application.sealed)
  in
  let root_bindings = specification_bindings runtime_env root_env in
  let aliases =
    List.concat_map scopes.scopes ~f:(fun scope ->
        List.concat_map scope.structure.str_items ~f:(fun item ->
            match item.str_desc with
            | Tstr_module
                { mb_id = Some id; mb_expr; mb_name = { txt = Some name; _ }; _ } ->
                begin match mb_expr.mod_desc with
                | Tmod_ident (target, _) ->
                    let alias =
                      Option.value_map scope.owner ~default:(Path.Pident id)
                        ~f:(fun owner -> Path.Pdot (owner, name))
                    in
                    let target =
                      Env.normalize_module_path None scope.environment target
                      |> Proof_scopes.canonical_owner scopes
                    in
                    if Path.same alias (Path.Pident id) then [ (alias, target) ]
                    else [ (alias, target); (Path.Pident id, target) ]
                | _ -> []
                end
            | _ -> []))
  in
  let prefix names path =
    let rec check names path =
      match (names, path) with
      | [], _ -> true
      | name :: names, part :: path when String.equal name part -> check names path
      | _ -> false
    in
    check names path
  in
  let nested =
    List.filter scopes.scopes ~f:(fun scope ->
        Option.is_some scope.owner
        && Option.value_map only_ids ~default:true ~f:(fun ids ->
            Option.exists scope.declaration_id ~f:(fun id ->
                List.mem ids id ~equal:Ident.same))
        && Option.value_map only ~default:true ~f:(fun namespace ->
            prefix namespace scope.namespace))
  in
  let visible_sibling scope (previous_scope, _, _) =
    let parent =
      List.take scope.Proof_scopes.namespace (List.length scope.namespace - 1)
    in
    match List.rev previous_scope.Proof_scopes.namespace with
    | _ :: reversed_parent -> List.equal String.equal (List.rev reversed_parent) parent
    | [] -> false
  in
  let overlay_sibling env (previous_scope, _, bindings) =
    match (previous_scope.Proof_scopes.declaration_id, previous_scope.namespace) with
    | Some id, namespace when (not previous_scope.sealed) && not (List.is_empty bindings)
      ->
        let name = List.last_exn namespace in
        begin try
          match Env.find_module_by_name (Lident name) env with
          | Pident found, declaration when Ident.same found id ->
              begin match declaration.md_type with
              | Mty_signature signature ->
                  Env.add_module_declaration ~check:false id Mp_present
                    { declaration with md_type = Mty_signature (signature @ bindings) }
                    env
              | Mty_ident _ | Mty_functor _ | Mty_alias _ -> env
              end
          | _ -> env
        with Stdlib.Not_found -> env
        end
    | _ -> env
  in
  let refresh_aliases env owner =
    List.fold aliases ~init:env ~f:(fun env (alias, target) ->
        if not (Path.same target owner) then env
        else
          match alias with
          | Pident id ->
              begin try
                match Env.find_module_by_name (Lident (Ident.name id)) env with
                | Pident found, declaration when Ident.same found id ->
                    Env.add_module_declaration ~check:false id Mp_present declaration env
                | _ -> env
              with Stdlib.Not_found -> env
              end
          | Pdot _ | Papply _ | Pextra_ty _ -> env)
  in
  let abstract_resources scope base =
    let* declared = signature_ghost_modules ~comments scope in
    List.fold_result declared ~init:(base, [])
      ~f:(fun (base, resources) (parameter, modules) ->
        List.fold_result modules ~init:(base, resources)
          ~f:(fun (base, resources) declaration ->
            let name = declaration.S.ghost_module_name in
            let interface = declaration.ghost_module_interface in
            let at = name.pid_loc in
            let* signatures = Proof_library.signatures at in
            let* () =
              match
                Proof_library.find signatures (Proof_library.path_of_qualid interface)
              with
              | Some selected
                when selected.interface
                     && Proof_library.is_resource_algebra signatures selected ->
                  Ok ()
              | Some _ ->
                  Error
                    (Report.error Type (S.qualid_loc interface)
                       "An abstract proof module must name a ResourceAlgebra interface")
              | None ->
                  Error
                    (Report.error Type (S.qualid_loc interface)
                       "Unknown Raven library interface")
            in
            let backend =
              String.concat ~sep:"_"
                (scope.namespace
                @ [
                    Ident.name parameter;
                    name.pid_str;
                    Int.to_string at.loc_start.pos_cnum;
                  ])
            in
            let temporary = S.mk_id ~loc:at backend in
            let* generated_env, _, generated, _, _ =
              elaborate_proof_types ~add_standard:false ~allow_interfaces:true base None
                [
                  S.Proof_resource
                    {
                      resource_name = temporary;
                      resource_functor = interface;
                      resource_arguments = [];
                    };
                ]
            in
            let* generated =
              match generated with
              | [ resource ] -> Ok resource
              | _ ->
                  Error (Report.error Type at "An abstract resource could not be typed")
            in
            let hidden =
              List.fold (specification_bindings base generated_env) ~init:base
                ~f:(fun env -> function
                | Types.Sig_type (id, declaration, _, _) ->
                    Env.add_type ~check:false id declaration env
                | _ -> env)
            in
            let parameter_declaration = Env.find_module (Pident parameter) hidden in
            let* body =
              match Mtype.scrape hidden parameter_declaration.md_type with
              | Mty_signature body -> Ok body
              | Mty_ident _ | Mty_functor _ | Mty_alias _ ->
                  Error
                    (Report.error Type at
                       "A ghost module requires a named module signature")
            in
            let* () =
              if
                List.exists body ~f:(function
                  | Types.Sig_module (id, _, _, _, _) ->
                      String.equal (Ident.name id) name.pid_str
                  | _ -> false)
              then
                Error
                  (Report.error Type at
                     (Printf.sprintf "The module %s is already declared" name.pid_str))
              else Ok ()
            in
            let id = Ident.create_local name.pid_str in
            let generated_declaration =
              Env.find_module (Pident generated.resource_id) generated_env
            in
            let item =
              Types.Sig_module
                ( id,
                  Mp_present,
                  { generated_declaration with md_loc = at },
                  Trec_not,
                  Exported )
            in
            let env =
              Env.add_module_declaration ~check:false parameter Mp_present
                { parameter_declaration with md_type = Mty_signature (body @ [ item ]) }
                hidden
            in
            let path = Path.Pdot (Pident parameter, name.pid_str) in
            let type_path, _ =
              Env.find_type_by_name
                (Ldot
                   ( {
                       txt =
                         Ldot
                           ( { txt = Lident (Ident.name parameter); loc = at },
                             { txt = name.pid_str; loc = at } );
                       loc = at;
                     },
                     { txt = "t"; loc = at } ))
                env
            in
            let typ = Ctype.newconstr type_path [] in
            let operations =
              List.map generated.resource_operations ~f:(fun (operation, _, _) ->
                  let value = Env.find_value (Path.Pdot (path, operation)) env in
                  let inputs, output = function_arguments value.val_type in
                  (operation, inputs, output))
            in
            let descriptor =
              Datatypes.resource_type ~name:backend ~module_id:id ~at |> fun descriptor ->
              Datatypes.with_paths descriptor
                (Path.Pdot (path, "t") :: generated.resource_descriptor.paths)
            in
            let resource =
              {
                generated with
                resource_name = name.pid_str;
                resource_backend = backend;
                resource_scope = scope.owner;
                resource_path = path;
                resource_environment = env;
                resource_abstract = true;
                resource_type = typ;
                resource_id = id;
                resource_operations = operations;
                resource_descriptor = descriptor;
                resource_at = at;
              }
            in
            Ok (env, resources @ [ resource ])))
  in
  let public_functor_result scope =
    let rec result (expression : Typedtree.module_expr) =
      match expression.mod_desc with
      | Tmod_functor (_, body) | Tmod_constraint (body, _, Tmodtype_implicit, _) ->
          result body
      | Tmod_structure _ -> true
      | Tmod_constraint (_, _, Tmodtype_explicit _, _) -> false
      | Tmod_ident _ | Tmod_apply _ | Tmod_apply_unit _ | Tmod_unpack _ -> false
    in
    let parent =
      Option.value_map scope.Proof_scopes.parent ~default:scopes.root.structure
        ~f:(fun path ->
          Option.value_map (Proof_scopes.find_owner scopes (Some path))
            ~default:scopes.root.structure ~f:(fun scope -> scope.structure))
    in
    List.exists parent.str_items ~f:(fun item ->
        match item.str_desc with
        | Tstr_module { mb_id = Some id; mb_expr; _ } ->
            Option.exists scope.declaration_id ~f:(Ident.same id) && result mb_expr
        | _ -> false)
  in
  let* typed =
    List.fold_result nested ~init:[] ~f:(fun previous scope ->
        let declarations = Proof_scopes.declarations_in scopes scope in
        let proof =
          List.filter_map declarations ~f:(fun entry ->
              match entry.declaration with
              | S.Proof_type _ | Proof_function _ | Proof_resource _ | Proof_field _
              | Proof_au _ ->
                  Some entry.declaration
              | _ -> None)
        in
        let functor_ancestor =
          List.find scopes.scopes ~f:(fun ancestor ->
              prefix ancestor.Proof_scopes.namespace scope.namespace
              && not (List.is_empty ancestor.parameters))
        in
        let allowed_functor_proof =
          match functor_ancestor with
          | Some ancestor
            when Option.equal Ident.same ancestor.declaration_id scope.declaration_id
                 || Option.is_some scope.definition
                    && Option.equal Path.same scope.parent ancestor.owner ->
              begin match ancestor.parameters with
              | _ :: _ ->
                  List.for_all proof ~f:(function
                    | S.Proof_type _ | Proof_function _ | Proof_resource _ | Proof_field _
                    | Proof_au _ ->
                        true
                    | _ -> false)
              | [] -> false
              end
          | Some _ | None -> false
        in
        let* () =
          if
            List.is_empty proof
            || Option.is_none functor_ancestor
            || allowed_functor_proof
          then Ok ()
          else
            Report.unsupported
              (Option.value scope.proof_location ~default:scope.source_location)
              "A type, function, resource, field, or AU inside a functor proof"
        in
        let inherited =
          List.filter previous ~f:(fun (ancestor, _, _) ->
              prefix ancestor.Proof_scopes.namespace scope.namespace)
        in
        let known_resources =
          previous_resources
          @ List.concat_map previous ~f:(fun (_, (_, _, resources, _, _), _) -> resources)
        in
        let own_names =
          List.filter_map proof ~f:(function
            | S.Proof_type { type_name; _ } -> Some type_name.pid_str
            | Proof_function { function_name; _ } -> Some function_name.pid_str
            | Proof_resource { resource_name; _ } -> Some resource_name.pid_str
            | Proof_field { field_name; _ } -> Some field_name.pid_str
            | Proof_au { au_name; _ } -> Some au_name.pid_str
            | _ -> None)
        in
        let without_shadowed bindings =
          List.filter bindings ~f:(function
            | Types.Sig_type (id, _, _, _)
            | Sig_value (id, _, _)
            | Sig_module (id, _, _, _, _) ->
                not (List.mem own_names (Ident.name id) ~equal:String.equal)
            | _ -> true)
        in
        let base =
          add_spec_bindings
            ~source_modules:(source_module_ids scopes.root.structure)
            (without_shadowed root_bindings)
            scope.environment
        in
        let base =
          List.fold inherited ~init:base
            ~f:(fun env (ancestor, (ancestor_env, _, _, _, _), bindings) ->
              let inherited_bindings =
                if List.is_empty ancestor.Proof_scopes.parameters then bindings
                else specification_bindings ancestor.environment ancestor_env
              in
              add_spec_bindings (without_shadowed inherited_bindings) env)
        in
        let base =
          List.fold previous ~init:base ~f:(fun env previous_entry ->
              if visible_sibling scope previous_entry then
                let env = overlay_sibling env previous_entry in
                let previous_scope, _, _ = previous_entry in
                Option.value_map previous_scope.owner ~default:env ~f:(fun owner ->
                    refresh_aliases env owner)
              else env)
        in
        let* base, abstract_resources = abstract_resources scope base in
        let* env, types, resources, fields, aus =
          elaborate_proof_types ~add_standard:false
            ~allow_shadowing:(Option.is_some scope.definition)
            ~previous:([], known_resources @ abstract_resources, [], [])
            ~canonical_owner:(Proof_scopes.canonical_owner scopes)
            base None proof
        in
        let* () =
          match scope.definition with
          | None -> Ok ()
          | Some interface ->
              let at = S.qualid_loc interface in
              let* signatures = Proof_library.signatures at in
              let* selected =
                match
                  Proof_library.find signatures (Proof_library.path_of_qualid interface)
                with
                | Some selected -> Ok selected
                | None -> Error (Report.error Type at "Unknown Raven library interface")
              in
              let local = specification_bindings base env in
              let* () =
                if
                  List.exists local ~f:(function
                    | Types.Sig_type (id, _, _, _) -> String.equal (Ident.name id) "t"
                    | _ -> false)
                then Ok ()
                else
                  Error
                    (Report.error Type at
                       "A proof-defined resource algebra must declare type t")
              in
              let member name expected =
                let* expected =
                  match expected with
                  | Ok typ ->
                      Ok (Typetexp.transl_simple_type env ~closed:true typ).ctyp_type
                  | Error error -> Error error
                in
                match
                  List.find_map local ~f:(function
                    | Types.Sig_value (id, value, _)
                      when String.equal (Ident.name id) name ->
                        Some value.val_type
                    | _ -> None)
                with
                | None
                  when not
                         (List.exists selected.required_members ~f:(fun (_, required) ->
                              String.equal name required)) ->
                    Ok ()
                | None ->
                    Error
                      (Report.error Type at
                         (Printf.sprintf
                            "The proof-defined resource algebra is missing %s" name))
                | Some actual ->
                    if Ctype.is_equal env false [ actual ] [ expected ] then Ok ()
                    else
                      Error
                        (Report.error Type at
                           (Printf.sprintf
                              "The proof-defined resource algebra member %s has the \
                               wrong type"
                              name))
              in
              let* () =
                List.fold_result (Proof_library.member_operations signatures selected)
                  ~init:() ~f:(fun () operation ->
                    member operation.name
                      (Proof_library.operation_type ~at ~signature:selected
                         ~substitutions:[] operation))
              in
              List.fold_result (Proof_library.member_constants signatures selected)
                ~init:() ~f:(fun () (name, typ) ->
                  member name
                    (Proof_library.ocaml_type ~at ~signature:selected ~substitutions:[]
                       typ))
        in
        let* exported_ghosts =
          public_ghost_modules ?public_interface ~comments scopes scope
        in
        let resources =
          List.filter resources ~f:(fun resource ->
              not
                (List.exists known_resources ~f:(fun known ->
                     Ident.same known.resource_id resource.resource_id)))
          |> List.map ~f:(fun resource ->
              if resource.resource_abstract then
                { resource with resource_environment = env }
              else
                let path =
                  Option.value_map scope.owner ~default:(Path.Pident resource.resource_id)
                    ~f:(fun owner -> Path.Pdot (owner, resource.resource_name))
                in
                let module_paths =
                  if
                    (not (public_functor_result scope))
                    && List.exists exported_ghosts ~f:(fun declaration ->
                        String.equal declaration.S.ghost_module_name.pid_str
                          resource.resource_name)
                  then []
                  else
                    path
                    :: Option.to_list
                         (Option.map scope.declaration_id ~f:(fun id ->
                              Path.Pdot (Path.Pident id, resource.resource_name)))
                    @ List.filter_map aliases ~f:(fun (alias, target) ->
                        Option.bind scope.owner ~f:(fun owner ->
                            Option.some_if (Path.same target owner)
                              (Path.Pdot (alias, resource.resource_name))))
                in
                let descriptor =
                  Datatypes.with_paths resource.resource_descriptor
                    (List.map module_paths ~f:(fun path -> Path.Pdot (path, "t")))
                in
                let aliases =
                  List.map resource.resource_aliases ~f:(fun alias ->
                      let member =
                        match alias.Datatypes.library with
                        | Some (Pdot (_, member)) -> member
                        | _ -> "element"
                      in
                      Datatypes.with_paths alias
                        (List.map module_paths ~f:(fun path -> Path.Pdot (path, member))))
                in
                {
                  resource with
                  resource_scope = scope.owner;
                  resource_path = path;
                  resource_environment = env;
                  resource_descriptor = descriptor;
                  resource_aliases = aliases;
                })
        in
        let owned_definitions =
          List.filter known_resources ~f:(fun resource ->
              resource.resource_definition
              && Option.equal Path.same resource.resource_scope scope.owner)
          |> List.map ~f:(fun resource ->
              if
                (not (public_functor_result scope))
                && List.exists exported_ghosts ~f:(fun declaration ->
                    String.equal declaration.S.ghost_module_name.pid_str
                      resource.resource_name)
              then resource
              else
                {
                  resource with
                  resource_descriptor =
                    Datatypes.with_paths resource.resource_descriptor
                      [ Path.Pdot (resource.resource_path, "t") ];
                })
        in
        let resources = owned_definitions @ resources in
        let* resources =
          List.fold_result exported_ghosts ~init:resources
            ~f:(fun resources declaration ->
              let name = declaration.S.ghost_module_name in
              let at = name.pid_loc in
              let* private_resource =
                match
                  List.find resources ~f:(fun resource ->
                      String.equal resource.resource_name name.pid_str)
                with
                | Some resource -> Ok resource
                | None ->
                    Error
                      (Report.error Type at
                         (Printf.sprintf
                            "The source module export %s has no proof implementation"
                            name.pid_str))
              in
              let* signatures = Proof_library.signatures at in
              let interface =
                Proof_library.path_of_qualid declaration.ghost_module_interface
              in
              let* selected =
                match Proof_library.find signatures interface with
                | Some selected
                  when selected.interface
                       && Proof_library.is_resource_algebra signatures selected ->
                    Ok selected
                | Some _ ->
                    Error
                      (Report.error Type at
                         "An exported proof module must name a ResourceAlgebra interface")
                | None -> Error (Report.error Type at "Unknown Raven library interface")
              in
              let* () =
                if
                  private_resource.resource_is_ra
                  && (List.equal String.equal private_resource.resource_functor
                        selected.path
                     || List.exists private_resource.resource_interfaces
                          ~f:(List.equal String.equal selected.path))
                then Ok ()
                else
                  Error
                    (Report.error Type at
                       "The exported proof module does not implement its interface")
              in
              let* () =
                if List.is_empty private_resource.resource_parameters then Ok ()
                else
                  Report.unsupported at
                    "Exporting a parameterized resource algebra through a nullary \
                     interface"
              in
              let temporary =
                S.mk_id ~loc:at
                  (Compiler_types.internal_name ~at (name.pid_str ^ "_public"))
              in
              let* generated_env, _, generated, _, _ =
                elaborate_proof_types ~add_standard:false ~allow_interfaces:true base None
                  [
                    S.Proof_resource
                      {
                        resource_name = temporary;
                        resource_functor = declaration.ghost_module_interface;
                        resource_arguments = [];
                      };
                  ]
              in
              let* generated =
                match generated with
                | [ resource ] -> Ok resource
                | _ -> Error (Report.error Type at "A public resource could not be typed")
              in
              let owner = Option.value_exn scope.owner in
              let public_path = Path.Pdot (owner, name.pid_str) in
              let public_id = Ident.create_local name.pid_str in
              let substitution =
                Subst.add_module generated.resource_id public_path Subst.identity
              in
              let substitution =
                List.fold generated.resource_type_members ~init:substitution
                  ~f:(fun substitution (member, id, _) ->
                    if String.equal member "T" then
                      Subst.add_type id (Path.Pdot (public_path, "t")) substitution
                    else substitution)
              in
              let generated_declaration =
                Env.find_module (Pident generated.resource_id) generated_env
              in
              let* public_signature =
                match generated_declaration.md_type with
                | Mty_signature body ->
                    let body = Subst.signature Keep substitution body in
                    Ok
                      (List.map body ~f:(function
                        | Types.Sig_type (id, declaration, rec_status, visibility)
                          when String.equal (Ident.name id) "t" ->
                            Types.Sig_type
                              ( id,
                                { declaration with type_manifest = None },
                                rec_status,
                                visibility )
                        | item -> item))
                | Mty_ident _ | Mty_functor _ | Mty_alias _ ->
                    Error (Report.error Type at "A public resource must be a module")
              in
              let public_declaration =
                { generated_declaration with md_type = Mty_signature public_signature }
              in
              let public_env =
                Env.add_module_declaration ~check:false public_id Mp_present
                  public_declaration generated_env
              in
              let resource_type = Ctype.newconstr (Path.Pdot (public_path, "t")) [] in
              let descriptor =
                Datatypes.resource_type ~name:name.pid_str ~module_id:public_id ~at
                |> fun descriptor ->
                Datatypes.with_paths descriptor [ Path.Pdot (public_path, "t") ]
              in
              let public =
                {
                  generated with
                  resource_name = name.pid_str;
                  resource_backend = name.pid_str ^ "_public";
                  resource_scope = scope.owner;
                  resource_path = public_path;
                  resource_environment = public_env;
                  resource_functor = selected.path;
                  resource_alias_of = None;
                  resource_abstract = false;
                  resource_type_members = [];
                  resource_type;
                  resource_id = public_id;
                  resource_operations =
                    List.map generated.resource_operations
                      ~f:(fun (operation, inputs, output) ->
                        ( operation,
                          List.map inputs ~f:(Subst.type_expr substitution),
                          Subst.type_expr substitution output ));
                  resource_descriptor = descriptor;
                  resource_aliases = [];
                  resource_at = at;
                  resource_public = None;
                  resource_application = None;
                }
              in
              Ok
                (List.map resources ~f:(fun resource ->
                     if Ident.same resource.resource_id private_resource.resource_id then
                       { resource with resource_public = Some public }
                     else resource)))
        in
        let fields =
          let private_t =
            if Option.is_none scope.definition then None
            else
              List.find_map types ~f:(fun data ->
                  Option.bind data.Datatypes.id ~f:(fun id ->
                      Option.some_if (String.equal data.module_name "T") (Path.Pident id)))
          in
          List.map fields ~f:(fun field ->
              let field_resource =
                match (private_t, Types.get_desc field.field_value) with
                | Some private_t, Tconstr (path, [], _) when Path.same path private_t ->
                    Option.bind scope.owner ~f:(fun owner ->
                        List.find_map known_resources ~f:(fun resource ->
                            Option.some_if
                              (Path.same owner resource.resource_path)
                              (Path.Pident resource.resource_id)))
                | _ -> field.field_resource
              in
              {
                field with
                field_scope = scope.owner;
                field_resource;
                field_path =
                  Option.value_map scope.owner ~default:field.field_path ~f:(fun owner ->
                      Path.Pdot (owner, field.field_name));
                field_environment = env;
              })
        in
        let aus =
          List.map aus ~f:(fun au ->
              let path =
                Option.value_map scope.owner ~default:au.au_path ~f:(fun owner ->
                    Path.Pdot (owner, au.au_name))
              in
              let module_paths =
                path
                :: Option.to_list
                     (Option.map scope.declaration_id ~f:(fun id ->
                          Path.Pdot (Path.Pident id, au.au_name)))
                @ List.filter_map aliases ~f:(fun (alias, target) ->
                    Option.bind scope.owner ~f:(fun owner ->
                        Option.some_if (Path.same target owner)
                          (Path.Pdot (alias, au.au_name))))
              in
              let token_paths =
                au.au_token_path
                :: List.map module_paths ~f:(fun path -> Path.Pdot (path, "token"))
              in
              {
                au with
                au_scope = scope.owner;
                au_path = path;
                au_environment = env;
                au_token_paths = List.dedup_and_sort token_paths ~compare:Path.compare;
              })
        in
        let namespaced =
          List.map types ~f:(fun data ->
              let name =
                String.capitalize
                  (String.concat ~sep:"_" (scope.namespace @ [ data.module_name ]))
              in
              let data = Datatypes.with_name data name in
              match (scope.owner, data.id) with
              | Some owner, Some id ->
                  let paths =
                    if Option.is_some scope.definition then []
                    else
                      [ Path.Pdot (owner, Ident.name id) ]
                      @ Option.to_list
                          (Option.map scope.declaration_id ~f:(fun module_id ->
                               Path.Pdot (Path.Pident module_id, Ident.name id)))
                      @ List.filter_map aliases ~f:(fun (alias, target) ->
                          Option.some_if (Path.same target owner)
                            (Path.Pdot (alias, Ident.name id)))
                  in
                  Datatypes.with_paths data paths
              | _ -> data)
        in
        let bindings = specification_bindings base env in
        let bindings =
          bindings
          @ List.map owned_definitions ~f:(fun resource ->
              let declaration =
                Env.find_module (Pident resource.resource_id) scope.environment
              in
              Types.Sig_module
                (resource.resource_id, Mp_present, declaration, Trec_not, Exported))
        in
        Ok (previous @ [ (scope, (env, namespaced, resources, fields, aus), bindings) ]))
  in
  let module_chain scope =
    List.mapi scope.Proof_scopes.namespace ~f:(fun index name ->
        let namespace = List.take scope.namespace (index + 1) in
        Option.map (Proof_scopes.find_namespace scopes namespace) ~f:(fun member ->
            (name, member.declaration_id, member.sealed)))
    |> Option.all
  in
  let rec extend_functor_result env typ bindings =
    match Mtype.scrape env typ with
    | Mty_signature signature -> Some (Types.Mty_signature (signature @ bindings))
    | Mty_functor (parameter, result) ->
        Option.map (extend_functor_result env result bindings) ~f:(fun result ->
            Types.Mty_functor (parameter, result))
    | Mty_ident _ | Mty_alias _ -> None
  in
  let rec extend_signature env signature chain bindings =
    match chain with
    | [] -> signature @ bindings
    | (name, Some id, _) :: rest ->
        let target =
          if
            List.exists signature ~f:(function
              | Types.Sig_module (found, _, _, _, _) -> Ident.same found id
              | _ -> false)
          then Some id
          else
            List.find_map (List.rev signature) ~f:(function
              | Types.Sig_module (found, _, _, _, _)
                when String.equal (Ident.name found) name ->
                  Some found
              | _ -> None)
        in
        List.map signature ~f:(function
          | Types.Sig_module (found, presence, declaration, rec_status, visibility)
            when Option.exists target ~f:(Ident.same found)
                 && String.equal (Ident.name found) name ->
              let declaration =
                match Mtype.scrape env declaration.md_type with
                | Mty_signature body ->
                    {
                      declaration with
                      md_type = Mty_signature (extend_signature env body rest bindings);
                    }
                | Mty_functor _ when List.is_empty rest ->
                    Option.value_map
                      (extend_functor_result env declaration.md_type bindings)
                      ~default:declaration ~f:(fun md_type ->
                        { declaration with md_type })
                | Mty_ident _ | Mty_functor _ | Mty_alias _ -> declaration
              in
              Types.Sig_module (found, presence, declaration, rec_status, visibility)
          | item -> item)
    | (_, None, _) :: _ -> signature
  in
  let qualified_env =
    List.fold typed ~init:root_env ~f:(fun env (scope, _, bindings) ->
        match module_chain scope with
        | Some ((name, Some id, _) :: rest as chain)
          when (not (List.is_empty bindings))
               && List.for_all chain ~f:(fun (_, _, sealed) -> not sealed)
               && (List.is_empty scope.parameters || public_functor_result scope) ->
            begin match Env.find_module_by_name (Lident name) env with
            | Pident found, declaration when Ident.same found id ->
                begin match Mtype.scrape env declaration.md_type with
                | Mty_signature signature ->
                    let signature = extend_signature env signature rest bindings in
                    Env.add_module_declaration ~check:false id Mp_present
                      { declaration with md_type = Mty_signature signature }
                      env
                | Mty_functor _ when List.is_empty rest ->
                    Option.value_map
                      (extend_functor_result env declaration.md_type bindings)
                      ~default:env ~f:(fun md_type ->
                        Env.add_module_declaration ~check:false id Mp_present
                          { declaration with md_type } env)
                | Mty_ident _ | Mty_functor _ | Mty_alias _ -> env
                end
            | _ -> env
            end
        | _ -> env)
  in
  let qualified_env =
    List.fold typed ~init:qualified_env ~f:(fun env (scope, (_, _, resources, _, _), _) ->
        match module_chain scope with
        | Some ((root_name, Some root_id, _) :: rest)
          when not (public_functor_result scope) ->
            List.fold resources ~init:env ~f:(fun env resource ->
                match resource.resource_public with
                | None -> env
                | Some public ->
                    let declaration =
                      Env.find_module (Pident public.resource_id)
                        public.resource_environment
                    in
                    let member =
                      Types.Sig_module
                        (public.resource_id, Mp_present, declaration, Trec_not, Exported)
                    in
                    begin match Env.find_module_by_name (Lident root_name) env with
                    | Pident found, root when Ident.same found root_id ->
                        let patched =
                          match Mtype.scrape env root.md_type with
                          | Mty_signature signature ->
                              Some
                                (Types.Mty_signature
                                   (extend_signature env signature rest [ member ]))
                          | Mty_functor _ when List.is_empty rest ->
                              extend_functor_result env root.md_type [ member ]
                          | Mty_ident _ | Mty_functor _ | Mty_alias _ -> None
                        in
                        Option.value_map patched ~default:env ~f:(fun md_type ->
                            Env.add_module_declaration ~check:false root_id Mp_present
                              { root with md_type } env)
                    | _ -> env
                    end)
        | _ -> env)
  in
  let application_carriers = ref [] in
  let qualified_env, projected_applications =
    List.fold applications ~init:(qualified_env, [])
      ~f:(fun (env, projected) (application : Functor_context.application) ->
        let template =
          List.find typed ~f:(fun (scope, _, bindings) ->
              (not (List.is_empty bindings))
              && Functor_context.same_scope scope application.scope
              && public_functor_result scope)
        in
        begin match template with
        | None -> (env, projected)
        | Some (scope, (_, _, resources, _, _), bindings) ->
            let identity = application.applicative_identity in
            let carrier_identity = Env.normalize_module_path None env identity in
            let env =
              List.fold resources ~init:env ~f:(fun env resource ->
                  List.fold resource.resource_type_members ~init:env
                    ~f:(fun env (_, hidden, declaration) ->
                      let existing =
                        List.find !application_carriers ~f:(fun (identity, member, _) ->
                            Path.same identity carrier_identity
                            && Ident.same member hidden)
                      in
                      match existing with
                      | Some _ -> env
                      | None ->
                          let anchor =
                            Ident.create_local
                              (Compiler_types.internal_name ~at:resource.resource_at
                                 (resource.resource_name ^ "_app"))
                          in
                          application_carriers :=
                            (carrier_identity, hidden, anchor) :: !application_carriers;
                          Env.add_type ~check:false anchor declaration env))
            in
            let substitution = Functor_context.substitution application in
            let substitution =
              List.fold (source_type_ids scope.structure) ~init:substitution
                ~f:(fun substitution (id, name) ->
                  Subst.add_type id (Path.Pdot (identity, name)) substitution)
            in
            let substitution =
              List.fold !application_carriers ~init:substitution
                ~f:(fun substitution (key, hidden, anchor) ->
                  if Path.same key carrier_identity then
                    Subst.add_type hidden (Path.Pident anchor) substitution
                  else substitution)
            in
            let bindings = Subst.signature Keep substitution bindings in
            let bindings =
              if Path.same carrier_identity application.result then bindings
              else
                match
                  Mtype.strengthen ~aliasable:true env (Mty_signature bindings)
                    carrier_identity
                with
                | Mty_signature bindings -> bindings
                | Mty_ident _ | Mty_functor _ | Mty_alias _ -> bindings
            in
            let env =
              match application.chain with
              | (root_name, root_id) :: rest ->
                  let rest =
                    List.map rest ~f:(fun (name, id) -> (name, Some id, false))
                  in
                  begin match Env.find_module_by_name (Lident root_name) env with
                  | Pident found, declaration when Ident.same found root_id ->
                      begin match Mtype.scrape env declaration.md_type with
                      | Mty_signature signature ->
                          Env.add_module_declaration ~check:false root_id Mp_present
                            {
                              declaration with
                              md_type =
                                Mty_signature
                                  (extend_signature env signature rest bindings);
                            }
                            env
                      | Mty_ident _ | Mty_functor _ | Mty_alias _ -> env
                      end
                  | _ -> env
                  end
              | [] -> env
            in
            (env, (application, bindings) :: projected)
        end)
  in
  let qualified_env =
    List.fold aliases ~init:qualified_env ~f:(fun env (alias, _) ->
        match alias with
        | Path.Pident id ->
            begin try
              match Env.find_module_by_name (Lident (Ident.name id)) env with
              | Pident found, declaration when Ident.same found id ->
                  Env.add_module_declaration ~check:false id Mp_present declaration env
              | _ -> env
            with Stdlib.Not_found -> env
            end
        | Pdot _ | Papply _ | Pextra_ty _ -> env)
  in
  let application_resources =
    List.concat_map applications ~f:(fun (application : Functor_context.application) ->
        let template =
          List.find typed ~f:(fun (scope, _, _) ->
              Functor_context.same_scope scope application.scope)
        in
        match template with
        | Some (scope, (_, _, resources, _, _), _) ->
            let view_owner = application.result in
            let carrier_identity =
              Env.normalize_module_path None qualified_env
                application.applicative_identity
            in
            List.filter resources ~f:(fun resource ->
                (not resource.resource_abstract)
                && Option.equal Path.same resource.resource_scope scope.owner)
            |> List.map ~f:(fun resource ->
                let view_path = Path.Pdot (view_owner, resource.resource_name) in
                let project ~private_resource original =
                  let id =
                    Ident.create_local
                      (if private_resource then
                         Compiler_types.internal_name ~at:original.resource_at
                           (original.resource_name ^ "_app")
                       else original.resource_name)
                  in
                  let path = Path.Pdot (view_owner, original.resource_name) in
                  let substitution =
                    Functor_context.substitution application
                    |> Subst.add_module original.resource_id path
                  in
                  let substitution =
                    List.fold original.resource_type_members ~init:substitution
                      ~f:(fun substitution (_, hidden, _) ->
                        let anchor =
                          List.find_map !application_carriers
                            ~f:(fun (key, member, anchor) ->
                              Option.some_if
                                (Path.same key carrier_identity
                                && Ident.same member hidden)
                                anchor)
                        in
                        let target =
                          Option.value_map anchor
                            ~default:(Path.Pdot (path, "t"))
                            ~f:(fun anchor -> Path.Pident anchor)
                        in
                        Subst.add_type hidden target substitution)
                  in
                  let original =
                    Source_type_map.resource original ~f:(Subst.type_expr substitution)
                  in
                  let descriptor =
                    Datatypes.resource_type ~name:original.resource_name ~module_id:id
                      ~at:original.resource_at
                  in
                  let descriptor =
                    { descriptor with parameters = original.resource_parameters }
                  in
                  let descriptor =
                    if Option.is_some original.resource_public then descriptor
                    else
                      let owners =
                        Functor_context.result_paths application
                        @ List.filter_map aliases ~f:(fun (alias, target) ->
                            Option.some_if
                              (Path.same target carrier_identity
                              || List.exists
                                   (Functor_context.result_paths application)
                                   ~f:(Path.same target))
                              alias)
                        |> List.dedup_and_sort ~compare:Path.compare
                      in
                      Datatypes.with_paths descriptor
                        (List.map owners ~f:(fun owner ->
                             Path.Pdot (Path.Pdot (owner, original.resource_name), "t")))
                  in
                  {
                    original with
                    resource_scope = None;
                    resource_path = path;
                    resource_environment = qualified_env;
                    resource_arguments =
                      List.map original.resource_arguments ~f:(function
                        | Type_argument _ as argument -> argument
                        | Module_argument path ->
                            Module_argument (Subst.module_path substitution path));
                    resource_alias_of =
                      Option.map original.resource_alias_of
                        ~f:(Subst.module_path substitution);
                    resource_type_members = [];
                    resource_type =
                      Ctype.newconstr (Path.Pdot (path, "t")) original.resource_parameters;
                    resource_id = id;
                    resource_descriptor = descriptor;
                    resource_aliases =
                      List.map original.resource_aliases ~f:(fun alias ->
                          let member =
                            match alias.Datatypes.library with
                            | Some (Pdot (_, member)) -> member
                            | _ -> "element"
                          in
                          {
                            (Datatypes.library_type ~library:original.resource_name
                               ~library_id:id ~at:original.resource_at member)
                            with
                            parameters = alias.parameters;
                            alias = alias.alias;
                          });
                    resource_public = None;
                    resource_application = Some (carrier_identity, original.resource_id);
                  }
                in
                let projected = project ~private_resource:true resource in
                let public =
                  Option.map resource.resource_public ~f:(fun public ->
                      {
                        (project ~private_resource:false public) with
                        resource_path = view_path;
                      })
                in
                { projected with resource_public = public })
        | _ -> [])
  in
  let qualified_env =
    List.fold application_resources ~init:qualified_env ~f:(fun env resource ->
        match resource.resource_application with
        | None -> env
        | Some (identity, template_id) ->
            let template =
              List.find_map typed ~f:(fun (scope, (_, _, resources, _, _), _) ->
                  Option.map
                    (List.find resources ~f:(fun original ->
                         Ident.same original.resource_id template_id))
                    ~f:(fun original -> (scope, original)))
            in
            let application =
              List.find applications
                ~f:(fun (application : Functor_context.application) ->
                  Path.same identity
                    (Env.normalize_module_path None env application.applicative_identity))
            in
            begin match (application, template) with
            | Some application, Some (scope, original)
              when Functor_context.same_scope scope application.scope ->
                let substitution = Functor_context.substitution application in
                let substitution =
                  List.fold (source_type_ids scope.structure) ~init:substitution
                    ~f:(fun substitution (id, name) ->
                      Subst.add_type id (Path.Pdot (identity, name)) substitution)
                in
                let substitution =
                  List.fold !application_carriers ~init:substitution
                    ~f:(fun substitution (key, hidden, anchor) ->
                      if Path.same key identity then
                        Subst.add_type hidden (Path.Pident anchor) substitution
                      else substitution)
                in
                let substitution =
                  Subst.add_module original.resource_id (Path.Pident resource.resource_id)
                    substitution
                in
                let declaration =
                  Env.find_module (Path.Pident original.resource_id)
                    original.resource_environment
                  |> Subst.module_declaration Keep substitution
                in
                let declaration =
                  match original.resource_alias_of with
                  | Some alias_of ->
                      {
                        declaration with
                        md_type = Mty_alias (Subst.module_path substitution alias_of);
                      }
                  | None -> declaration
                in
                Env.add_module_declaration ~check:false resource.resource_id Mp_present
                  declaration env
            | _ -> env
            end)
  in
  let qualified_env =
    List.fold application_resources ~init:qualified_env ~f:(fun env resource ->
        match
          (resource.resource_path, resource.resource_public, resource.resource_application)
        with
        | Path.Pdot (Pident result_id, name), Some public, Some (identity, template_id) ->
            let template =
              List.find_map typed ~f:(fun (scope, (_, _, resources, _, _), _) ->
                  Option.bind
                    (List.find resources ~f:(fun original ->
                         Ident.same original.resource_id template_id))
                    ~f:(fun original ->
                      Option.map original.resource_public ~f:(fun exported ->
                          (scope, exported))))
            in
            begin match template with
            | None -> env
            | Some (scope, _) when public_functor_result scope -> env
            | Some (scope, template_public) ->
                let carrier_identity = identity in
                let declaration =
                  Env.find_module (Path.Pident template_public.resource_id)
                    template_public.resource_environment
                in
                let env, anchor =
                  let existing =
                    List.find !application_carriers ~f:(fun (key, member, _) ->
                        Path.same key carrier_identity
                        && Ident.same member template_public.resource_id)
                  in
                  match existing with
                  | Some (_, _, anchor) -> (env, Some anchor)
                  | None ->
                      begin match declaration.md_type with
                      | Mty_signature body ->
                          begin match
                            List.find_map body ~f:(function
                              | Types.Sig_type (id, typ, _, _)
                                when String.equal (Ident.name id) "t" ->
                                  Some typ
                              | _ -> None)
                          with
                          | None -> (env, None)
                          | Some typ ->
                              let anchor =
                                Ident.create_local
                                  (Compiler_types.internal_name
                                     ~at:template_public.resource_at
                                     (template_public.resource_name ^ "_public_app"))
                              in
                              application_carriers :=
                                (carrier_identity, template_public.resource_id, anchor)
                                :: !application_carriers;
                              (Env.add_type ~check:false anchor typ env, Some anchor)
                          end
                      | Mty_ident _ | Mty_functor _ | Mty_alias _ -> (env, None)
                      end
                in
                let substitution =
                  Option.value_map scope.declaration_id ~default:Subst.identity
                    ~f:(fun id ->
                      Subst.add_module id (Path.Pident result_id) Subst.identity)
                  |> Subst.add_module template_public.resource_id public.resource_path
                in
                let declaration =
                  match declaration.md_type with
                  | Mty_signature body ->
                      let body = Subst.signature Keep substitution body in
                      let body =
                        List.map body ~f:(function
                          | Types.Sig_type (id, typ, rec_status, visibility)
                            when String.equal (Ident.name id) "t" ->
                              let typ =
                                Option.value_map anchor ~default:typ ~f:(fun anchor ->
                                    {
                                      typ with
                                      type_manifest =
                                        Some (Ctype.newconstr (Path.Pident anchor) []);
                                    })
                              in
                              Types.Sig_type (id, typ, rec_status, visibility)
                          | item -> item)
                      in
                      { declaration with md_type = Mty_signature body }
                  | Mty_ident _ | Mty_functor _ | Mty_alias _ -> declaration
                in
                let member =
                  Types.Sig_module
                    (public.resource_id, Mp_present, declaration, Trec_not, Exported)
                in
                begin match
                  Env.find_module_by_name (Lident (Ident.name result_id)) env
                with
                | Pident found, result when Ident.same found result_id ->
                    begin match Mtype.scrape env result.md_type with
                    | Mty_signature signature ->
                        let signature =
                          List.filter signature ~f:(function
                            | Types.Sig_module (id, _, _, _, _) ->
                                not (String.equal (Ident.name id) name)
                            | _ -> true)
                        in
                        Env.add_module_declaration ~check:false result_id Mp_present
                          { result with md_type = Mty_signature (signature @ [ member ]) }
                          env
                    | Mty_ident _ | Mty_functor _ | Mty_alias _ -> env
                    end
                | _ -> env
                end
            end
        | _ -> env)
  in
  let qualified_env =
    List.fold aliases ~init:qualified_env ~f:(fun env (alias, _) ->
        match alias with
        | Path.Pident id ->
            begin try
              match Env.find_module_by_name (Lident (Ident.name id)) env with
              | Pident found, declaration when Ident.same found id ->
                  Env.add_module_declaration ~check:false id Mp_present declaration env
              | _ -> env
            with Stdlib.Not_found -> env
            end
        | Pdot _ | Papply _ | Pextra_ty _ -> env)
  in
  let application_aus =
    List.concat_map applications ~f:(fun (application : Functor_context.application) ->
        let template =
          List.find typed ~f:(fun (scope, _, _) ->
              Functor_context.same_scope scope application.scope)
        in
        match template with
        | Some (scope, (_, _, _, _, aus), _) ->
            let view_owner = application.result in
            let identity = application.applicative_identity in
            let carrier_identity =
              Env.normalize_module_path None qualified_env identity
            in
            let substitution = Functor_context.substitution application in
            let substitution =
              List.fold (source_type_ids scope.structure) ~init:substitution
                ~f:(fun substitution (id, name) ->
                  Subst.add_type id (Path.Pdot (identity, name)) substitution)
            in
            List.filter aus ~f:(fun au -> Option.equal Path.same au.au_scope scope.owner)
            |> List.map ~f:(fun au ->
                let path = Path.Pdot (view_owner, au.au_name) in
                let token_path = Path.Pdot (path, "token") in
                let identity_path = Path.Pdot (carrier_identity, au.au_name) in
                let token_paths =
                  List.map (Functor_context.result_paths application) ~f:(fun owner ->
                      Path.Pdot (Path.Pdot (owner, au.au_name), "token"))
                  @ [ Path.Pdot (identity_path, "token") ]
                  @ List.filter_map aliases ~f:(fun (alias, target) ->
                      Option.some_if
                        (Path.same target carrier_identity
                        || List.exists
                             (Functor_context.result_paths application)
                             ~f:(Path.same target))
                        (Path.Pdot (Path.Pdot (alias, au.au_name), "token")))
                  |> List.dedup_and_sort ~compare:Path.compare
                in
                let operation_path =
                  Option.value_map (scoped_value_name scope au.au_operation_path)
                    ~default:(Subst.module_path substitution au.au_operation_path)
                    ~f:(fun name -> Path.Pdot (view_owner, name))
                in
                let related =
                  Compiler_types.map_group
                    (au.au_parameters @ [ au.au_operation_type; au.au_token ])
                    ~f:(Subst.type_expr substitution)
                in
                let parameters, operation =
                  List.split_n related (List.length au.au_parameters)
                in
                let operation_type = List.nth_exn operation 0 in
                let token_arguments =
                  match Types.get_desc (List.nth_exn operation 1) with
                  | Tconstr (_, arguments, _) -> arguments
                  | _ -> failwith "An AU token projection must preserve its constructor"
                in
                {
                  au with
                  au_scope = None;
                  au_id = Ident.create_local au.au_name;
                  au_path = path;
                  au_environment = qualified_env;
                  au_operation_path = operation_path;
                  au_operation_type = operation_type;
                  au_parameters = parameters;
                  au_token =
                    Btype.newgenty
                      (Types.get_desc (Ctype.newconstr token_path token_arguments));
                  au_token_path = token_path;
                  au_token_paths = token_paths;
                  au_application = Some (carrier_identity, au.au_id);
                })
        | _ -> [])
  in
  let private_root env caller root_id =
    let root = Env.find_module (Pident root_id) qualified_env in
    let ancestors =
      List.init (List.length caller.Proof_scopes.namespace) ~f:(fun index ->
          Proof_scopes.find_namespace scopes (List.take caller.namespace (index + 1)))
      |> Option.all
    in
    let own scope =
      List.find_map typed ~f:(fun (candidate, _, bindings) ->
          Option.some_if
            (Option.equal Ident.same candidate.declaration_id
               scope.Proof_scopes.declaration_id)
            bindings)
      |> Option.value ~default:[]
    in
    let direct_applications signature =
      List.fold projected_applications ~init:signature
        ~f:(fun signature (application, bindings) ->
          match List.rev application.Functor_context.chain with
          | (name, id) :: reversed_parent ->
              let parent = List.rev_map reversed_parent ~f:(fun (name, _) -> name) in
              if List.equal String.equal parent caller.namespace then
                extend_signature env signature [ (name, Some id, false) ] bindings
              else signature
          | [] -> signature)
    in
    let rec private_type (scopes : Proof_scopes.scope list) =
      match scopes with
      | [] -> None
      | [ scope ] ->
          Some
            (Types.Mty_signature
               (direct_applications (scope.structure.str_type @ own scope)))
      | scope :: (child :: _ as rest) ->
          Option.map (private_type rest) ~f:(fun child_type ->
              let signature = scope.structure.str_type @ own scope in
              let signature =
                List.map signature ~f:(function
                  | Types.Sig_module (id, presence, declaration, rec_status, visibility)
                    when Option.exists child.declaration_id ~f:(Ident.same id) ->
                      Types.Sig_module
                        ( id,
                          presence,
                          { declaration with md_type = child_type },
                          rec_status,
                          visibility )
                  | item -> item)
              in
              Types.Mty_signature signature)
    in
    match ancestors with
    | Some (first :: _ as ancestors)
      when Option.exists first.declaration_id ~f:(Ident.same root_id)
           && List.for_all ancestors ~f:(fun scope ->
               List.is_empty scope.Proof_scopes.parameters) ->
        Option.value_map (private_type ancestors) ~default:root ~f:(fun md_type ->
            { root with md_type })
    | Some [] | Some (_ :: _) | None -> root
  in
  let scopes =
    Proof_scopes.map_environments scopes ~f:(fun scope ->
        let env =
          match
            List.find typed ~f:(fun (candidate, _, _) ->
                Option.equal Ident.same candidate.declaration_id scope.declaration_id)
          with
          | Some (_, (env, _, _, _, _), _) -> env
          | None ->
              if Option.is_none scope.owner then qualified_env else scope.environment
        in
        List.fold applications ~init:env
          ~f:(fun env (application : Functor_context.application) ->
            match List.rev application.chain with
            | (_, id) :: parent ->
                let namespace = List.rev_map parent ~f:(fun (name, _) -> name) in
                if List.equal String.equal scope.namespace namespace then
                  begin try
                    let env =
                      match application.chain with
                      | (_, root_id) :: _ when not (List.is_empty parent) ->
                          let root = private_root env scope root_id in
                          Env.add_module_declaration ~check:false root_id Mp_present root
                            env
                      | _ -> env
                    in
                    let local = Env.find_module (Pident id) env in
                    let md_type =
                      if Path.same application.result (Pident id) then
                        (Env.find_module application.result qualified_env).md_type
                      else Types.Mty_alias application.result
                    in
                    let env =
                      Env.add_module_declaration ~check:false id Mp_present
                        { local with md_type } env
                    in
                    List.fold aliases ~init:env ~f:(fun env (alias, target) ->
                        match alias with
                        | Pident alias_id
                          when List.exists
                                 (Functor_context.result_paths application)
                                 ~f:(Path.same target)
                               && List.exists scope.structure.str_items ~f:(fun item ->
                                   match item.Typedtree.str_desc with
                                   | Tstr_module { mb_id = Some id; _ } ->
                                       Ident.same id alias_id
                                   | _ -> false) ->
                            begin try
                              let declaration = Env.find_module (Pident alias_id) env in
                              Env.add_module_declaration ~check:false alias_id Mp_present
                                {
                                  declaration with
                                  md_type = Types.Mty_alias application.result;
                                }
                                env
                            with Stdlib.Not_found -> env
                            end
                        | Pident _ | Pdot _ | Papply _ | Pextra_ty _ -> env)
                  with Stdlib.Not_found -> env
                  end
                else env
            | [] -> env))
  in
  let types = List.concat_map typed ~f:(fun (_, (_, types, _, _, _), _) -> types) in
  let resources =
    List.concat_map typed ~f:(fun (_, (_, _, resources, _, _), _) -> resources)
    @ List.map application_resources ~f:(fun resource ->
        {
          resource with
          resource_environment = qualified_env;
          resource_public =
            Option.map resource.resource_public ~f:(fun public ->
                { public with resource_environment = qualified_env });
        })
  in
  let* () =
    List.fold_result scopes.scopes ~init:() ~f:(fun () scope ->
        if public_functor_result scope then Ok ()
        else
          let* occurrences =
            public_ghost_occurrences ?public_interface ~comments scopes scope
          in
          List.fold_result occurrences ~init:() ~f:(fun () (suffix, declaration) ->
              match (scope.owner, suffix) with
              | Some owner, _ :: _ ->
                  let path =
                    List.fold suffix ~init:owner ~f:(fun path name ->
                        Path.Pdot (path, name))
                    |> fun path -> Path.Pdot (path, declaration.ghost_module_name.pid_str)
                  in
                  let at = declaration.ghost_module_name.pid_loc in
                  let* selected =
                    let* signatures = Proof_library.signatures at in
                    match
                      Proof_library.find signatures
                        (Proof_library.path_of_qualid declaration.ghost_module_interface)
                    with
                    | Some selected when selected.interface -> Ok selected
                    | Some _ | None ->
                        Error
                          (Report.error Type at
                             "Unknown nested resource algebra interface")
                  in
                  let inner =
                    List.find (previous_resources @ resources) ~f:(fun resource ->
                        Path.same resource.resource_path path)
                  in
                  begin match inner with
                  | Some { resource_public = Some public; _ }
                    when List.equal String.equal public.resource_functor selected.path ->
                      Ok ()
                  | Some _ ->
                      Error
                        (Report.error Type at
                           "A nested resource algebra export changes interface across \
                            source seals")
                  | None ->
                      Error
                        (Report.error Type at
                           "A nested resource algebra export has no proof implementation")
                  end
              | Some _, [] | None, _ -> Ok ()))
  in
  let fields = List.concat_map typed ~f:(fun (_, (_, _, _, fields, _), _) -> fields) in
  let aus =
    List.concat_map typed ~f:(fun (_, (_, _, _, _, aus), _) -> aus)
    @ List.map application_aus ~f:(fun au -> { au with au_environment = qualified_env })
  in
  Ok (qualified_env, scopes, types, resources, fields, aus)

let signature_ghost_resources env comments =
  Annotation.of_comments comments
  |> List.filter ~f:(fun annotation ->
      Poly.equal (Annotation.kind annotation) Annotation.Ghost_module)
  |> List.fold_result ~init:[] ~f:(fun resources annotation ->
      let* declaration = Annotation.ghost_module annotation in
      let name = declaration.S.ghost_module_name in
      let at = name.pid_loc in
      let* signatures = Proof_library.signatures at in
      let* selected =
        match
          Proof_library.find signatures
            (Proof_library.path_of_qualid declaration.ghost_module_interface)
        with
        | Some selected
          when selected.interface && Proof_library.is_resource_algebra signatures selected
          ->
            Ok selected
        | Some _ ->
            Error
              (Report.error Type at
                 "An abstract proof module must name a ResourceAlgebra interface")
        | None -> Error (Report.error Type at "Unknown Raven library interface")
      in
      let temporary =
        S.mk_id ~loc:at (Compiler_types.internal_name ~at (name.pid_str ^ "_signature"))
      in
      let* generated_env, _, generated, _, _ =
        elaborate_proof_types ~add_standard:false ~allow_interfaces:true env None
          [
            S.Proof_resource
              {
                resource_name = temporary;
                resource_functor = declaration.ghost_module_interface;
                resource_arguments = [];
              };
          ]
      in
      let* generated =
        match generated with
        | [ resource ] -> Ok resource
        | _ -> Error (Report.error Type at "A signature resource could not be typed")
      in
      let id = Ident.create_local name.pid_str in
      let path = Path.Pident id in
      let substitution = Subst.add_module generated.resource_id path Subst.identity in
      let substitution =
        List.fold generated.resource_type_members ~init:substitution
          ~f:(fun substitution (member, hidden, _) ->
            if String.equal member "T" then
              Subst.add_type hidden (Path.Pdot (path, "t")) substitution
            else substitution)
      in
      let generated_declaration =
        Env.find_module (Pident generated.resource_id) generated_env
      in
      let* body =
        match generated_declaration.md_type with
        | Mty_signature body ->
            Ok
              (Subst.signature Keep substitution body
              |> List.map ~f:(function
                | Types.Sig_type (id, typ, rec_status, visibility)
                  when String.equal (Ident.name id) "t" ->
                    Types.Sig_type
                      (id, { typ with type_manifest = None }, rec_status, visibility)
                | item -> item))
        | Mty_ident _ | Mty_functor _ | Mty_alias _ ->
            Error (Report.error Type at "A signature resource must be a module")
      in
      let environment =
        Env.add_module_declaration ~check:false id Mp_present
          { generated_declaration with md_type = Mty_signature body; md_loc = at }
          generated_env
      in
      let resource =
        {
          generated with
          resource_name = name.pid_str;
          resource_backend = Compiler_types.internal_name ~at (name.pid_str ^ "_signature");
          resource_scope = None;
          resource_path = path;
          resource_environment = environment;
          resource_functor = selected.path;
          resource_alias_of = None;
          resource_abstract = true;
          resource_type = Ctype.newconstr (Path.Pdot (path, "t")) [];
          resource_id = id;
          resource_operations =
            List.map generated.resource_operations ~f:(fun (operation, args, result) ->
                ( operation,
                  List.map args ~f:(Subst.type_expr substitution),
                  Subst.type_expr substitution result ));
          resource_descriptor =
            Datatypes.resource_type ~name:name.pid_str ~module_id:id ~at;
          resource_aliases = [];
          resource_at = at;
          resource_public = None;
          resource_application = None;
        }
      in
      Ok (resources @ [ (at, resource) ]))

let signature_resource source (declaration : S.ghost_module) =
  let at = declaration.ghost_module_name.pid_loc in
  match
    List.find source.signature_resources ~f:(fun (location, _) ->
        Declaration_scope.same_place location at)
  with
  | Some (_, resource) -> Ok resource
  | None -> Error (Report.error Type at "The signature resource is not declared")

let signature_ghost_environment source declarations env =
  List.fold_result declarations ~init:env ~f:(fun env declaration ->
      let* resource = signature_resource source declaration in
      let env =
        List.fold resource.resource_type_members ~init:env ~f:(fun env (_, id, typ) ->
            Env.add_type ~check:false id typ env)
      in
      let module_declaration =
        Env.find_module (Pident resource.resource_id) resource.resource_environment
      in
      Ok
        (Env.add_module_declaration ~check:false resource.resource_id Mp_present
           module_declaration env))

let realize_signature_ghost_environment source ~substitution declarations env =
  let* env = signature_ghost_environment source declarations env in
  List.fold_result declarations ~init:env ~f:(fun env declaration ->
      let* resource = signature_resource source declaration in
      let path = Subst.module_path substitution (Path.Pident resource.resource_id) in
      if Path.same path (Path.Pident resource.resource_id) then Ok env
      else
        let views =
          List.concat_map source.proof_resources ~f:(fun resource ->
              Option.to_list resource.resource_public @ [ resource ])
        in
        let actual =
          Option.first_some
            (List.find views ~f:(fun resource ->
                 Path.same path (Pident resource.resource_id)))
            (List.find views ~f:(fun resource -> resource_has_path resource path))
        in
        let env =
          Option.value_map actual ~default:env ~f:(fun actual ->
              let env =
                List.fold actual.resource_type_members ~init:env
                  ~f:(fun env (_, id, typ) -> Env.add_type ~check:false id typ env)
              in
              let source_environment = actual.resource_environment in
              let rec module_roots path =
                match path with
                | Path.Pident id -> [ id ]
                | Pdot (parent, _) | Pextra_ty (parent, _) -> module_roots parent
                | Papply (fn, argument) -> module_roots fn @ module_roots argument
              in
              let env =
                List.fold (module_roots path) ~init:env ~f:(fun env id ->
                    let find source_env =
                      try Some (Env.find_module (Pident id) source_env)
                      with Stdlib.Not_found -> None
                    in
                    let binding =
                      Option.first_some (find source.env) (find source_environment)
                    in
                    Option.value_map binding ~default:env ~f:(fun binding ->
                        Env.add_module_declaration ~check:false id Mp_present binding env))
              in
              let actual_declaration =
                try Some (Env.find_module (Pident actual.resource_id) source_environment)
                with Stdlib.Not_found -> None
              in
              Option.value_map actual_declaration ~default:env ~f:(fun binding ->
                  Env.add_module_declaration ~check:false actual.resource_id Mp_present
                    binding env))
        in
        let original =
          Env.find_module (Pident resource.resource_id) resource.resource_environment
        in
        Ok
          (Env.add_module_declaration ~check:false resource.resource_id Mp_present
             { original with md_type = Mty_alias path }
             env))

let imported_proof_resources env libraries =
  let within = Declaration_scope.contains in
  let children signature =
    List.filter_map signature ~f:(function
      | Types.Sig_module (_, _, declaration, _, _) -> Some declaration.md_loc
      | Sig_modtype (_, declaration, _) -> Some declaration.mtd_loc
      | _ -> None)
  in
  let rec append env signature names member =
    match names with
    | [] -> signature @ [ member ]
    | name :: rest ->
        List.map signature ~f:(function
          | Types.Sig_module (id, presence, declaration, rec_status, visibility)
            when String.equal (Ident.name id) name ->
              let declaration =
                match Mtype.scrape env declaration.md_type with
                | Mty_signature body ->
                    {
                      declaration with
                      md_type = Mty_signature (append env body rest member);
                    }
                | Mty_ident _ | Mty_functor _ | Mty_alias _ -> declaration
              in
              Types.Sig_module (id, presence, declaration, rec_status, visibility)
          | item -> item)
  in
  List.fold_result libraries ~init:(env, []) ~f:(fun (env, resources) library ->
      let library_module = Env.find_module (Pident library.library_id) env in
      let* signature =
        match Mtype.scrape env library_module.md_type with
        | Mty_signature body -> Ok body
        | Mty_ident _ | Mty_functor _ | Mty_alias _ ->
            Error
              (Report.error Type library.library.scope.location
                 "An imported interface must be a module signature")
      in
      let annotations = Annotation.of_comments library.library.interface_comments in
      let rec collect path names location signature =
        let nested = children signature in
        let direct =
          List.filter annotations ~f:(fun annotation ->
              Poly.equal (Annotation.kind annotation) Annotation.Ghost_module
              && within location annotation.loc
              && not (List.exists nested ~f:(fun child -> within child annotation.loc)))
        in
        let* direct = Result.all (List.map direct ~f:Annotation.ghost_module) in
        let* () =
          List.fold_result direct ~init:() ~f:(fun () declaration ->
              let name = declaration.S.ghost_module_name in
              if
                List.exists signature ~f:(function
                  | Types.Sig_module (id, _, _, _, _) ->
                      String.equal (Ident.name id) name.pid_str
                  | _ -> false)
              then
                Error
                  (Report.error Type name.pid_loc
                     (Printf.sprintf "The module %s is already declared" name.pid_str))
              else Ok ())
        in
        let* descendants =
          Result.all
            (List.filter_map signature ~f:(function
              | Types.Sig_module (id, _, declaration, _, _) ->
                  begin match Mtype.scrape env declaration.md_type with
                  | Mty_signature body ->
                      Some
                        (collect
                           (Path.Pdot (path, Ident.name id))
                           (names @ [ Ident.name id ])
                           declaration.md_loc body)
                  | Mty_ident _ | Mty_functor _ | Mty_alias _ -> None
                  end
              | _ -> None))
        in
        Ok
          (List.map direct ~f:(fun declaration -> (path, names, declaration))
          @ List.concat descendants)
      in
      let* declarations =
        collect (Pident library.library_id) [ library.library_name ]
          library.library.scope.location signature
      in
      List.fold_result declarations ~init:(env, resources)
        ~f:(fun (env, resources) (owner, names, declaration) ->
          let name = declaration.S.ghost_module_name in
          let at = name.pid_loc in
          let* signatures = Proof_library.signatures at in
          let* selected =
            match
              Proof_library.find signatures
                (Proof_library.path_of_qualid declaration.ghost_module_interface)
            with
            | Some selected
              when selected.interface
                   && Proof_library.is_resource_algebra signatures selected ->
                Ok selected
            | Some _ ->
                Error
                  (Report.error Type at
                     "An imported proof module must name a ResourceAlgebra interface")
            | None -> Error (Report.error Type at "Unknown Raven library interface")
          in
          let* () =
            if
              List.exists resources ~f:(fun resource ->
                  Path.same resource.resource_path (Path.Pdot (owner, name.pid_str)))
            then
              Error
                (Report.error Type at
                   (Printf.sprintf "The module %s is already declared" name.pid_str))
            else Ok ()
          in
          let temporary =
            S.mk_id ~loc:at (Compiler_types.internal_name ~at name.pid_str)
          in
          let* generated_env, _, generated, _, _ =
            elaborate_proof_types ~add_standard:false ~allow_interfaces:true env None
              [
                S.Proof_resource
                  {
                    resource_name = temporary;
                    resource_functor = declaration.ghost_module_interface;
                    resource_arguments = [];
                  };
              ]
          in
          let* generated =
            match generated with
            | [ resource ] -> Ok resource
            | _ -> Error (Report.error Type at "An imported resource could not be typed")
          in
          let path = Path.Pdot (owner, name.pid_str) in
          let id = Ident.create_local name.pid_str in
          let substitution = Subst.add_module generated.resource_id path Subst.identity in
          let substitution =
            List.fold generated.resource_type_members ~init:substitution
              ~f:(fun substitution (member, hidden, _) ->
                if String.equal member "T" then
                  Subst.add_type hidden (Path.Pdot (path, "t")) substitution
                else substitution)
          in
          let generated_declaration =
            Env.find_module (Pident generated.resource_id) generated_env
          in
          let* body =
            match generated_declaration.md_type with
            | Mty_signature body ->
                Ok
                  (Subst.signature Keep substitution body
                  |> List.map ~f:(function
                    | Types.Sig_type (id, declaration, rec_status, visibility)
                      when String.equal (Ident.name id) "t" ->
                        Types.Sig_type
                          ( id,
                            { declaration with type_manifest = None },
                            rec_status,
                            visibility )
                    | item -> item))
            | Mty_ident _ | Mty_functor _ | Mty_alias _ ->
                Error (Report.error Type at "An imported resource must be a module")
          in
          let member =
            Types.Sig_module
              ( id,
                Mp_present,
                { generated_declaration with md_type = Mty_signature body; md_loc = at },
                Trec_not,
                Exported )
          in
          let root = Env.find_module (Pident library.library_id) env in
          let* root_signature =
            match Mtype.scrape env root.md_type with
            | Mty_signature body -> Ok body
            | Mty_ident _ | Mty_functor _ | Mty_alias _ ->
                Error (Report.error Type at "An imported library must be a module")
          in
          let env =
            Env.add_module_declaration ~check:false library.library_id Mp_present
              {
                root with
                md_type =
                  Mty_signature (append env root_signature (List.tl_exn names) member);
              }
              env
          in
          let descriptor =
            Datatypes.resource_type ~name:name.pid_str ~module_id:id ~at
            |> fun descriptor -> Datatypes.with_paths descriptor [ Path.Pdot (path, "t") ]
          in
          let resource =
            {
              generated with
              resource_name = name.pid_str;
              resource_backend = String.concat ~sep:"_" (names @ [ name.pid_str ]);
              resource_scope = None;
              resource_path = path;
              resource_environment = env;
              resource_functor = selected.path;
              resource_alias_of = None;
              resource_abstract = true;
              resource_type_members = [];
              resource_type = Ctype.newconstr (Path.Pdot (path, "t")) [];
              resource_id = id;
              resource_operations =
                List.map generated.resource_operations
                  ~f:(fun (operation, args, result) ->
                    ( operation,
                      List.map args ~f:(Subst.type_expr substitution),
                      Subst.type_expr substitution result ));
              resource_descriptor = descriptor;
              resource_aliases = [];
              resource_at = at;
              resource_public = None;
              resource_application = None;
            }
          in
          Ok (env, resources @ [ resource ])))
