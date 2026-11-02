(** An OCaml implementation, parsed and type-checked by the compiler's own front end, with
    its interface and proof, if there are any: [f.mli] and [f.proof] next to [f.ml]. *)

open Base
include Source_core

let annotation_env ?at source lexical_env =
  let source_modules =
    source_module_ids source.typed
    @ List.concat_map source.proof_scopes.scopes ~f:(fun scope ->
        source_module_ids scope.Proof_scopes.structure)
  in
  let env = add_spec_bindings ~source_modules source.spec_bindings lexical_env in
  let contains = Declaration_scope.contains in
  let same_declaration a b = (not (Poly.equal a Location.none)) && Poly.equal a b in
  let previous_summary = function
    | Env.Env_empty -> None
    | Env_value (previous, _, _)
    | Env_type (previous, _, _)
    | Env_module (previous, _, _, _)
    | Env_modtype (previous, _, _)
    | Env_extension (previous, _, _)
    | Env_class (previous, _, _)
    | Env_cltype (previous, _, _)
    | Env_open (previous, _)
    | Env_not_aliasable (previous, _)
    | Env_constraints (previous, _)
    | Env_copy_types previous
    | Env_persistent (previous, _)
    | Env_value_unbound (previous, _, _)
    | Env_module_unbound (previous, _, _) ->
        Some previous
  in
  let rec matching_module name loc (summary : Env.summary) =
    match summary with
    | Env_module (_, id, _, declaration)
      when String.equal (Ident.name id) name && same_declaration loc declaration.md_loc ->
        Some (Path.Pident id)
    | _ -> Option.bind (previous_summary summary) ~f:(matching_module name loc)
  in
  let rec matching_type name loc (summary : Env.summary) =
    match summary with
    | Env_type (_, id, declaration)
      when String.equal (Ident.name id) name && same_declaration loc declaration.type_loc
      ->
        Some (Path.Pident id)
    | _ -> Option.bind (previous_summary summary) ~f:(matching_type name loc)
  in
  match at with
  | None -> env
  | Some at ->
      let scope =
        List.filter source.proof_scopes.scopes ~f:(fun scope ->
            contains scope.Proof_scopes.source_location at)
        |> List.max_elt ~compare:(fun a b ->
            Int.compare
              (List.length a.Proof_scopes.namespace)
              (List.length b.Proof_scopes.namespace))
      in
      Option.value_map scope ~default:env ~f:(fun scope ->
          let bindings =
            specification_bindings scope.structure.str_final_env scope.environment
          in
          let parameter_projection =
            List.filter_map scope.parameters ~f:(function
              | Named (Some parameter, _, _) ->
                  begin try
                    let original =
                      Env.find_module (Pident parameter) scope.structure.str_final_env
                    in
                    Option.bind
                      (matching_module (Ident.name parameter) original.md_loc
                         (Env.summary lexical_env))
                      ~f:(fun path ->
                        Option.some_if
                          (not (Path.same path (Pident parameter)))
                          (parameter, path))
                  with Stdlib.Not_found -> None
                  end
              | Unit | Named (None, _, _) -> None)
          in
          let substitution, changed =
            match parameter_projection with
            | [] -> (Subst.identity, false)
            | _ :: _ ->
                let substitution =
                  List.fold parameter_projection ~init:Subst.identity
                    ~f:(fun substitution (parameter, path) ->
                      Subst.add_module parameter path substitution)
                in
                List.fold (source_type_ids scope.structure) ~init:(substitution, true)
                  ~f:(fun (substitution, changed) (id, name) ->
                    try
                      let original =
                        Env.find_type (Pident id) scope.structure.str_final_env
                      in
                      begin match
                        matching_type name original.type_loc (Env.summary lexical_env)
                      with
                      | Some path when not (Path.same path (Pident id)) ->
                          (Subst.add_type id path substitution, true)
                      | Some _ | None -> (substitution, changed)
                      end
                    with Stdlib.Not_found -> (substitution, changed))
          in
          let bindings =
            if not changed then bindings
            else
              List.map bindings ~f:(function
                | Types.Sig_type (id, declaration, rec_status, visibility) ->
                    Types.Sig_type
                      ( id,
                        Subst.type_declaration substitution declaration,
                        rec_status,
                        visibility )
                | Sig_value (id, description, visibility) ->
                    Sig_value
                      (id, Subst.value_description substitution description, visibility)
                | item -> item)
          in
          add_spec_bindings ~source_modules bindings env)

let project_ghost_parameter source ~original ~target lexical_env =
  let resources =
    List.filter source.proof_resources ~f:(fun resource ->
        resource.resource_abstract
        &&
        match resource.resource_path with
        | Path.Pdot (Pident parameter, _) -> Ident.same parameter original
        | Pident _ | Pdot _ | Papply _ | Pextra_ty _ -> false)
  in
  match resources with
  | [] -> Ok lexical_env
  | first :: _ ->
      let at = first.resource_at in
      let error message = Error (Report.error Type at message) in
      let compiler f =
        try Ok (f ())
        with exn ->
          Error
            (Option.value (Report.of_exn exn)
               ~default:(Report.error Type at (Stdlib.Printexc.to_string exn)))
      in
      let* scope =
        match
          List.find source.proof_scopes.scopes ~f:(fun scope ->
              List.exists scope.Proof_scopes.parameters ~f:(function
                | Typedtree.Named (Some id, _, _) -> Ident.same id original
                | Unit | Named (None, _, _) -> false))
        with
        | Some scope -> Ok scope
        | None -> error "The abstract proof parameter has no source scope"
      in
      let* original_signature =
        let* module_type =
          compiler (fun () ->
              let declaration = Env.find_module (Pident original) scope.environment in
              Mtype.scrape scope.environment declaration.md_type)
        in
        match module_type with
        | Mty_signature members -> Ok members
        | Mty_ident _ | Mty_functor _ | Mty_alias _ ->
            error "The abstract proof parameter has no signature"
      in
      let names = List.map resources ~f:(fun resource -> resource.resource_name) in
      let ghost_members =
        List.filter original_signature ~f:(function
          | Types.Sig_module (id, _, _, _, _) ->
              List.mem names (Ident.name id) ~equal:String.equal
          | _ -> false)
      in
      let* () =
        if List.length ghost_members = List.length resources then Ok ()
        else error "An abstract proof module is missing from its parameter signature"
      in
      let* lexical_env =
        compiler (fun () ->
            List.fold resources ~init:lexical_env ~f:(fun env resource ->
                List.fold resource.resource_type_members ~init:env
                  ~f:(fun env (_, id, declaration) ->
                    Env.add_type ~check:false id declaration env)))
      in
      let* target_declaration =
        compiler (fun () -> Env.find_module (Pident target) lexical_env)
      in
      let* target_signature =
        let* module_type =
          compiler (fun () -> Mtype.scrape lexical_env target_declaration.md_type)
        in
        match module_type with
        | Mty_signature members -> Ok members
        | Mty_ident _ | Mty_functor _ | Mty_alias _ ->
            error "The specialized proof parameter has no signature"
      in
      let target_signature =
        List.filter target_signature ~f:(function
          | Types.Sig_module (id, _, _, _, _) ->
              not (List.mem names (Ident.name id) ~equal:String.equal)
          | _ -> true)
      in
      compiler (fun () ->
          Env.add_module_declaration ~check:false target Mp_present
            {
              target_declaration with
              md_type = Mty_signature (target_signature @ ghost_members);
            }
            lexical_env)

(** The file next to [file] with the extension [ext] instead of its own, if it exists. *)
let sibling file ext =
  let other = Stdlib.Filename.remove_extension file ^ ext in
  Option.some_if (Stdlib.Sys.file_exists other) other

let lexbuf_of file =
  let lexbuf = Lexing.from_string (Stdio.In_channel.read_all file) in
  Location.init lexbuf file;
  lexbuf

(** The interface in [file], parsed. *)
let load_interface file =
  let lexbuf = lexbuf_of file in
  Location.input_name := file;
  Lexer.init ();
  let signature = Parse.interface lexbuf in
  {
    signature;
    typed_signature = None;
    interface_comments = Lexer.comments ();
    scope = Declaration_scope.of_lexbuf ~file lexbuf;
  }

(** Uses OCaml's inclusion checker before specializing the implementation. *)
let check_interface env signature interface =
  try
    let declared = Typemod.type_interface env interface.signature in
    Includemod.check_implementation env signature declared.sig_type;
    Ok { interface with typed_signature = Some declared }
  with exn -> (
    match Report.of_exn exn with
    | Some error ->
        let loc =
          match interface.signature with
          | item :: _ when error.loc.loc_start.pos_lnum <= 0 -> item.psig_loc
          | _ -> error.loc
        in
        Error { error with loc }
    | None ->
        let loc =
          match interface.signature with
          | item :: _ -> item.psig_loc
          | [] -> Location.none
        in
        Error (Report.error Type loc (Stdlib.Printexc.to_string exn)))

(** Links the type variables of [impl], the type of a value, to what they stand for in
    [iface], the type its interface gives it, expanding abbreviations as needed. *)
let rec specialize env (impl : Types.type_expr) (iface : Types.type_expr) =
  let expanded t =
    let t' = Ctype.expand_head env t in
    Option.some_if (not (Types.eq_type t t')) t'
  in
  match (Types.get_desc impl, Types.get_desc iface) with
  | Tpoly (impl, []), _ -> specialize env impl iface
  | _, Tpoly (iface, []) -> specialize env impl iface
  | Tvar _, _ -> if not (Types.eq_type impl iface) then Types.link_type impl iface
  | Tarrow (_, a, r, _), Tarrow (_, a', r', _) ->
      specialize env a a';
      specialize env r r'
  | Ttuple ts, Ttuple ts' when List.length ts = List.length ts' ->
      List.iter2_exn ts ts' ~f:(fun (_, t) (_, t') -> specialize env t t')
  | Tconstr (p, args, _), Tconstr (p', args', _)
    when Path.same
           (Env.normalize_type_path None env p)
           (Env.normalize_type_path None env p')
         && List.length args = List.length args' ->
      List.iter2_exn args args' ~f:(specialize env)
  | _ ->
      begin match (expanded iface, expanded impl) with
      | Some iface, _ -> specialize env impl iface
      | None, Some impl -> specialize env impl iface
      | None, None -> ()
      end

(** Specializes the values of [typed] to the types that [interface] gives them: the
    translation is monomorphic, and an interface fixes the types of the values it
    declares. *)
let specialize_to_interface _env (typed : Typedtree.structure)
    (interface : interface option) =
  let exported_value signature name =
    List.find_map signature ~f:(function
      | Types.Sig_value (id, description, Exported) when String.equal (Ident.name id) name
        ->
          Some (id, description)
      | _ -> None)
  in
  let exported_type signature name =
    List.find_map signature ~f:(function
      | Types.Sig_type (id, _, _, Exported) when String.equal (Ident.name id) name ->
          Some id
      | _ -> None)
  in
  let exported_module signature name =
    List.find_map signature ~f:(function
      | Types.Sig_module (id, _, declaration, _, Exported)
        when String.equal (Ident.name id) name ->
          Some (id, declaration)
      | _ -> None)
  in
  let rec structure signature_env substitution (typed : Typedtree.structure) signature =
    let signature_env = Env.add_signature signature signature_env in
    let substitution =
      List.fold signature ~init:substitution ~f:(fun substitution -> function
        | Types.Sig_type (id, _, _, Exported) ->
            Option.value_map
              (exported_type typed.str_type (Ident.name id))
              ~default:substitution
              ~f:(fun body -> Subst.add_type id (Pident body) substitution)
        | Sig_module (id, _, _, _, Exported) ->
            Option.value_map
              (exported_module typed.str_type (Ident.name id))
              ~default:substitution
              ~f:(fun (body, _) -> Subst.add_module id (Pident body) substitution)
        | _ -> substitution)
    in
    List.iter typed.str_items ~f:(fun item ->
        match item.str_desc with
        | Tstr_value (_, bindings) ->
            List.iter bindings ~f:(fun (vb : Typedtree.value_binding) ->
                match vb.vb_pat.pat_desc with
                | Tpat_var (id, _, _) ->
                    begin match exported_value signature (Ident.name id) with
                    | Some (_, description) ->
                        specialize typed.str_final_env vb.vb_expr.exp_type
                          (Subst.type_expr substitution description.val_type)
                    | None -> ()
                    end
                | _ -> ())
        | Tstr_module { mb_id = Some id; mb_expr; _ } ->
            begin match
              ( exported_module typed.str_type (Ident.name id),
                exported_module signature (Ident.name id) )
            with
            | Some (exported, _), Some (_, declaration) when Ident.same exported id ->
                view signature_env substitution mb_expr declaration.md_type
            | _ -> ()
            end
        | _ -> ())
  and view signature_env substitution (body : Typedtree.module_expr) signature =
    match body.mod_desc with
    | Tmod_constraint (body, _, _, _) -> view signature_env substitution body signature
    | Tmod_structure typed ->
        begin match Mtype.scrape signature_env signature with
        | Mty_signature signature -> structure signature_env substitution typed signature
        | Mty_ident _ | Mty_functor _ | Mty_alias _ -> ()
        end
    | Tmod_ident _ | Tmod_functor _ | Tmod_apply _ | Tmod_apply_unit _ | Tmod_unpack _ ->
        ()
  in
  let rec constraints (typed : Typedtree.structure) =
    List.iter typed.str_items ~f:(fun item ->
        match item.str_desc with
        | Tstr_module binding -> module_constraints binding.mb_expr
        | _ -> ())
  and module_constraints (body : Typedtree.module_expr) =
    match body.mod_desc with
    | Tmod_constraint (inner, signature, _, _) ->
        module_constraints inner;
        view body.mod_env Subst.identity inner signature
    | Tmod_structure typed -> constraints typed
    | Tmod_ident _ | Tmod_functor _ | Tmod_apply _ | Tmod_apply_unit _ | Tmod_unpack _ ->
        ()
  in
  constraints typed;
  Option.iter interface ~f:(fun interface ->
      Option.iter interface.typed_signature ~f:(fun declared ->
          structure declared.sig_final_env Subst.identity typed declared.sig_type))

(** The declarations of the proof in [file]. *)
let load_proof file : (S.proof_file, Report.error) Result.t =
  let lexbuf = lexbuf_of file in
  let lexeme_loc () =
    {
      Location.loc_start = Lexing.lexeme_start_p lexbuf;
      loc_end = Lexing.lexeme_end_p lexbuf;
      loc_ghost = false;
    }
  in
  try Ok (Caravan_spec.Spec_parser.proof Caravan_spec.Spec_lexer.token lexbuf) with
  | Caravan_spec.Spec_lexer.Error (loc, message) ->
      Error (Report.error Syntax loc message)
  | Caravan_spec.Spec_parser.Error ->
      Error (Report.error Syntax (lexeme_loc ()) "Syntax error")

(** The interfaces without an implementation next to them in [file]'s directory, then in
    [include_dirs] in order, each the first of its module's name; not [file]'s own. *)
let library_files ~include_dirs file =
  let own = Stdlib.Filename.(remove_extension (basename file)) in
  let in_dir dir =
    List.filter_map
      (List.sort (Array.to_list (Stdlib.Sys.readdir dir)) ~compare:String.compare)
      ~f:(fun f ->
        let base = Stdlib.Filename.remove_extension f in
        Option.some_if
          (Stdlib.Filename.check_suffix f ".mli"
          && (not (String.equal base own))
          && not (Stdlib.Sys.file_exists (Stdlib.Filename.concat dir (base ^ ".ml"))))
          (Stdlib.Filename.concat dir f))
  in
  List.concat_map (Stdlib.Filename.dirname file :: include_dirs) ~f:in_dir
  |> List.stable_dedup ~compare:(fun f g ->
      String.compare Stdlib.Filename.(basename f) Stdlib.Filename.(basename g))

(** Parses and type-checks [file], in the environment of the standard library and the
    libraries in its directory and [include_dirs]. The front end reports errors by
    raising; they are returned here. *)
let load ?(include_dirs = []) (file : string) : (t, Report.error) Result.t =
  try
    Compmisc.init_path ();
    (* Caravan reports what OCaml warns about that matters to it, as a non-exhaustive match. *)
    let (_ : Warnings.alert option) = Warnings.parse_options false "-a" in
    let env = Compmisc.initial_env () in
    let env, libraries =
      List.fold (library_files ~include_dirs file) ~init:(env, [])
        ~f:(fun (env, libraries) f ->
          let library = load_interface f in
          let library_name =
            String.capitalize Stdlib.Filename.(remove_extension (basename f))
          in
          let declaration =
            Ast_helper.Sig.module_
              (Ast_helper.Md.mk
                 (Location.mknoloc (Some library_name))
                 (Ast_helper.Mty.signature library.signature))
          in
          let typed = Typemod.type_interface env [ declaration ] in
          let library_id, typed_signature =
            match typed.sig_items with
            | [
             {
               sig_desc =
                 Tsig_module
                   { md_id = Some id; md_type = { mty_desc = Tmty_signature s; _ }; _ };
               _;
             };
            ] ->
                (id, Some s)
            | _ -> (Ident.create_local library_name, None)
          in
          let library = { library with typed_signature } in
          (typed.sig_final_env, { library_name; library_id; library } :: libraries))
    in
    let libraries = List.rev libraries in
    let text = Stdio.In_channel.read_all file in
    let lexbuf = Lexing.from_string text in
    Location.init lexbuf file;
    Location.input_name := file;
    Lexer.init ();
    let parsed = Parse.implementation lexbuf in
    let scope = Declaration_scope.of_lexbuf ~file lexbuf in
    let comments = Lexer.comments () in
    Env.set_current_unit
      (Unit_info.make ~check_modname:false ~source_file:file Impl
         (Stdlib.Filename.remove_extension file));
    let interface_env = env in
    let typed, signature, _, _, env = Typemod.type_structure env parsed in
    let runtime_env = env in
    let interface = Option.map (sibling file ".mli") ~f:load_interface in
    let* interface =
      match interface with
      | None -> Ok None
      | Some interface ->
          Result.map (check_interface interface_env signature interface) ~f:Option.some
    in
    (* Specifications have sequences and pending calls, which OCaml does not. *)
    let _, _, _, _, env =
      Typemod.type_structure env
        (Parse.implementation (Lexing.from_string "type 'a sequence type 'k pending"))
    in
    let sequence, _ = Env.find_type_by_name (Lident "sequence") env in
    let pending, _ = Env.find_type_by_name (Lident "pending") env in
    let env, logical_types =
      List.fold
        [
          ("finset", Datatypes.FinSet, "type 'a finset");
          ("set", Datatypes.Set, "type 'a set");
          ("map", Datatypes.Map, "type ('k, 'v) map");
        ]
        ~init:(env, [])
        ~f:(fun (env, types) (name, kind, declaration) ->
          match find_type_by_name env name with
          | Some _ -> (env, types)
          | None ->
              let _, _, _, _, env =
                Typemod.type_structure env
                  (Parse.implementation (Lexing.from_string declaration))
              in
              let types =
                match find_type_by_name env name with
                | Some (Pident id, _) -> Datatypes.collection id kind :: types
                | _ -> types
              in
              (env, types))
    in
    let env, logical_types =
      match find_type_by_name env "integer" with
      | Some _ -> (env, logical_types)
      | None ->
          let _, _, _, _, env =
            Typemod.type_structure env
              (Parse.implementation (Lexing.from_string "type integer = int"))
          in
          let logical_types =
            match find_type_by_name env "integer" with
            | Some (Pident id, _) -> Datatypes.logical_integer id :: logical_types
            | _ -> logical_types
          in
          (env, logical_types)
    in
    let logical_types = List.rev logical_types in
    specialize_to_interface env typed interface;
    let signature_comments =
      comments
      @ Option.value_map interface ~default:[] ~f:(fun interface ->
          interface.interface_comments)
      @ List.concat_map libraries ~f:(fun library -> library.library.interface_comments)
    in
    let proof_file = sibling file ".proof" in
    let proof =
      Option.value_map proof_file
        ~default:(Ok { S.declarations = []; outlines = [] })
        ~f:load_proof
    in
    Result.bind proof ~f:(fun ({ S.declarations = proof; _ } as proof_file_contents) ->
        let* outline_annotations =
          match proof_file with
          | None -> Ok []
          | Some proof_file ->
              Outline.annotations
                ~proof_text:(Stdio.In_channel.read_all proof_file)
                ~structure:parsed
                ~annotations:(Annotation.of_comments comments)
                proof_file_contents
        in
        let* env, _, _, _, _ = Proof_types.elaborate_proof_types env interface [] in
        let* signature_resources =
          Proof_types.signature_ghost_resources env signature_comments
        in
        let* env, imported_resources =
          Proof_types.imported_proof_resources env libraries
        in
        let prepare_definition (root_env, resources) parent module_name module_interface =
          let declaration =
            S.Proof_resource
              {
                resource_name = module_name;
                resource_functor = module_interface;
                resource_arguments = [];
              }
          in
          let* local_env, _, all_resources, _, _ =
            Proof_types.elaborate_proof_types ~add_standard:false ~allow_interfaces:true
              ~previous:([], resources, [], []) parent.Proof_scopes.environment None
              [ declaration ]
          in
          let* signatures = Proof_library.signatures module_name.pid_loc in
          let* selected =
            match
              Proof_library.find signatures
                (Proof_library.path_of_qualid module_interface)
            with
            | Some selected when selected.interface -> Ok selected
            | Some _ ->
                Error
                  (Report.error Type
                     (S.qualid_loc module_interface)
                     "A proof-defined module must name an interface")
            | None ->
                Error
                  (Report.error Type
                     (S.qualid_loc module_interface)
                     "Unknown Raven library interface")
          in
          let* () =
            if Proof_library.is_resource_algebra signatures selected then Ok ()
            else
              Error
                (Report.error Type
                   (S.qualid_loc module_interface)
                   "A proof-defined module must implement ResourceAlgebra")
          in
          let* new_resource =
            match
              List.filter all_resources ~f:(fun resource ->
                  not
                    (List.exists resources ~f:(fun known ->
                         Ident.same known.resource_id resource.resource_id)))
            with
            | [ resource ] -> Ok resource
            | _ ->
                Error
                  (Report.error Type module_name.pid_loc
                     "A proof-defined module could not be registered")
          in
          let path =
            Option.value_map parent.owner ~default:(Path.Pident new_resource.resource_id)
              ~f:(fun owner -> Path.Pdot (owner, module_name.pid_str))
          in
          let resource =
            {
              new_resource with
              resource_scope = parent.owner;
              resource_path = path;
              resource_environment = local_env;
              resource_definition = true;
            }
          in
          let root_env = if Option.is_none parent.owner then local_env else root_env in
          Ok
            ((root_env, resources @ [ resource ]), { parent with environment = local_env })
        in
        let* (env, definitions), proof_scopes =
          Proof_scopes.resolve_prepared ~location:scope.location ~environment:env
            ~state:(env, imported_resources) ~prepare_definition typed proof
        in
        let applications = Functor_context.collect proof_scopes in
        let merge_resources existing additions =
          List.fold additions ~init:existing ~f:(fun existing added ->
              if
                List.exists existing ~f:(fun resource ->
                    Ident.same resource.resource_id added.resource_id)
              then
                List.map existing ~f:(fun resource ->
                    if Ident.same resource.resource_id added.resource_id then added
                    else resource)
              else existing @ [ added ])
        in
        let initial = (env, [], [], definitions, [], [], proof_scopes) in
        Result.bind
          (List.fold_result proof ~init:initial
             ~f:(fun
                 (env, root_types, scoped_types, resources, fields, aus, proof_scopes)
                 declaration
               ->
               match declaration with
               | S.Proof_module { module_name; _ } ->
                   let* ( env,
                          proof_scopes,
                          types,
                          module_resources,
                          module_fields,
                          module_aus ) =
                     Proof_types.scoped_proof_types ~applications
                       ~only:[ module_name.pid_str ] ?public_interface:interface
                       ~comments:signature_comments ~previous_resources:resources
                       runtime_env env proof_scopes
                   in
                   Ok
                     ( env,
                       root_types,
                       scoped_types @ types,
                       merge_resources resources module_resources,
                       fields @ module_fields,
                       aus @ module_aus,
                       proof_scopes )
               | S.Proof_definition { module_name; _ } ->
                   let* ( env,
                          proof_scopes,
                          types,
                          module_resources,
                          module_fields,
                          module_aus ) =
                     Proof_types.scoped_proof_types ~applications
                       ~only:[ module_name.pid_str ] ?public_interface:interface
                       ~comments:signature_comments ~previous_resources:resources
                       runtime_env env proof_scopes
                   in
                   Ok
                     ( env,
                       root_types,
                       scoped_types @ types,
                       merge_resources resources module_resources,
                       fields @ module_fields,
                       aus @ module_aus,
                       proof_scopes )
               | declaration ->
                   let* env, root_types, resources, fields, aus =
                     Proof_types.elaborate_proof_types ~add_standard:false
                       ~previous:(root_types, resources, fields, aus)
                       ~complete_proof:proof env interface [ declaration ]
                   in
                   Ok (env, root_types, scoped_types, resources, fields, aus, proof_scopes)))
          ~f:(fun
              ( env,
                root_types,
                scoped_types,
                proof_resources,
                proof_fields,
                proof_aus,
                proof_scopes )
            ->
            let* proof_scopes, implicit =
              Proof_types.implicit_ghost_scopes ~comments:signature_comments proof_scopes
            in
            let* ( env,
                   proof_scopes,
                   implicit_types,
                   implicit_resources,
                   implicit_fields,
                   implicit_aus ) =
              match implicit with
              | [] -> Ok (env, proof_scopes, [], [], [], [])
              | _ ->
                  Proof_types.scoped_proof_types ~applications
                    ~only_ids:
                      (List.filter_map implicit ~f:(fun scope ->
                           scope.Proof_scopes.declaration_id))
                    ?public_interface:interface ~comments:signature_comments
                    ~previous_resources:proof_resources runtime_env env proof_scopes
            in
            let proof_scopes =
              Proof_scopes.map_environments proof_scopes ~f:(fun scope ->
                  if Option.is_none scope.owner then env else scope.environment)
            in
            let proof_types = root_types @ scoped_types @ implicit_types in
            let proof_applications =
              applications
              @ List.filter (Functor_context.collect proof_scopes)
                  ~f:(fun (application : Functor_context.application) ->
                    Option.is_none
                      (Functor_context.find_at applications application.location))
            in
            let* proof_resources =
              Result.all
                (List.map (proof_resources @ implicit_resources) ~f:(fun resource ->
                     if
                       (not resource.resource_definition)
                       || Option.is_some resource.resource_application
                     then Ok resource
                     else
                       let at = resource.resource_at in
                       let* definition =
                         match
                           List.find proof_scopes.scopes ~f:(fun scope ->
                               Option.exists scope.owner
                                 ~f:(Path.same resource.resource_path)
                               && Option.exists scope.declaration_id
                                    ~f:(Ident.same resource.resource_id))
                         with
                         | Some scope -> Ok scope
                         | None ->
                             Error
                               (Report.error Type at
                                  "A proof-defined resource has no owning scope")
                       in
                       let* type_id =
                         try
                           match
                             Env.find_type_by_name (Lident "t") definition.environment
                           with
                           | Pident id, _ -> Ok id
                           | _ ->
                               Error
                                 (Report.error Type at
                                    "A proof-defined resource algebra must declare type t")
                         with Stdlib.Not_found ->
                           Error
                             (Report.error Type at
                                "A proof-defined resource algebra must declare type t")
                       in
                       let* () =
                         if
                           List.exists proof_types ~f:(fun data ->
                               Option.exists data.Datatypes.id ~f:(Ident.same type_id))
                         then Ok ()
                         else
                           Error
                             (Report.error Type at
                                "A proof-defined resource algebra must declare type t")
                       in
                       Ok
                         {
                           resource with
                           resource_representation =
                             Some (Ctype.newconstr (Path.Pident type_id) []);
                         }))
            in
            Ok
              {
                file;
                text;
                scope;
                typed;
                comments;
                outline_annotations;
                env;
                sequence;
                logical_types;
                proof_types =
                  List.sort proof_types ~compare:(fun a b ->
                      Int.compare a.Datatypes.at.loc_start.pos_cnum
                        b.Datatypes.at.loc_start.pos_cnum);
                proof_resources;
                signature_resources;
                proof_fields = proof_fields @ implicit_fields;
                proof_aus = proof_aus @ implicit_aus;
                proof_applications;
                pending;
                interface;
                proof;
                proof_scopes;
                libraries;
                spec_bindings = specification_bindings runtime_env env;
              }))
  with exn -> (
    match Report.of_exn exn with
    | Some error -> Error error
    | None ->
        Error (Report.error Type (Location.in_file file) (Stdlib.Printexc.to_string exn)))

(** The OCaml type that the type [t] of an annotation at [at] denotes in [env]. The
    compiler's type checker reports errors by raising. *)
let ocaml_type (env : Env.t) ~(at : Location.t) (t : S.pty) :
    (Types.type_expr, Report.error) Result.t =
  try Ok (Typetexp.transl_simple_type env ~closed:true (core_type ~at t)).ctyp_type
  with exn -> (
    match Report.of_exn exn with
    | Some error -> Error error
    | None -> Error (Report.error Type at (Stdlib.Printexc.to_string exn)))

(** One scheme preserves the sharing of type variables across declaration parameters. *)
let ocaml_types env ~at types =
  match types with
  | [] -> Ok []
  | _ -> (
      try
        let core =
          match types with
          | [ typ ] -> core_type ~at typ
          | _ ->
              Ast_helper.Typ.tuple ~loc:at
                (List.map types ~f:(fun typ -> (None, core_type ~at typ)))
        in
        let typed =
          Typetexp.TyVarEnv.with_local_scope (fun () ->
              Typetexp.transl_type_scheme env core)
        in
        begin match types with
        | [ _ ] -> Ok [ typed.ctyp_type ]
        | _ ->
            begin match Types.get_desc typed.ctyp_type with
            | Ttuple components -> Ok (List.map components ~f:snd)
            | _ ->
                Error
                  (Report.error Type at "Expected a tuple of declaration parameter types")
            end
        end
      with exn ->
        begin match Report.of_exn exn with
        | Some error -> Error error
        | None -> Error (Report.error Type at (Stdlib.Printexc.to_string exn))
        end)

(** The opaque OCaml reference type of proof-only storage. *)
let ghost_type env ~at =
  ocaml_type env ~at
    (S.PTtyapp (Qdot (Qid (S.mk_id ~loc:at "Ghost"), S.mk_id ~loc:at "t"), []))

(** Compiler-only operations used to type-check logical expressions. *)
let logical_check_signature =
  "module Caravan__logical_check : sig\n\
   val quantify : ('a -> bool) -> bool\n\
   val implies : bool -> bool -> bool\n\
   val equal : 'a -> 'a -> bool\n\
   val not_equal : 'a -> 'a -> bool\n\
   val to_sequence : 'a list -> 'a sequence\n\
   module Set : sig\n\
   val empty : 'a set\n\
   val singleton : 'a -> 'a set\n\
   val mem : 'a -> 'a set -> bool\n\
   val union : 'a set -> 'a set -> 'a set\n\
   val inter : 'a set -> 'a set -> 'a set\n\
   val diff : 'a set -> 'a set -> 'a set\n\
   val subset : 'a set -> 'a set -> bool\n\
   val of_predicate : ('a -> bool) -> 'a set\n\
   end\n\
   module Finset : sig\n\
   val empty : 'a finset\n\
   val singleton : 'a -> 'a finset\n\
   val mem : 'a -> 'a finset -> bool\n\
   val union : 'a finset -> 'a finset -> 'a finset\n\
   val inter : 'a finset -> 'a finset -> 'a finset\n\
   val diff : 'a finset -> 'a finset -> 'a finset\n\
   val subset : 'a finset -> 'a finset -> bool\n\
   val choose : 'a finset -> 'a\n\
   end\n\
   module Map : sig\n\
   val const : 'v -> ('k,'v) map\n\
   val get : ('k,'v) map -> 'k -> 'v\n\
   val set : ('k,'v) map -> 'k -> 'v -> ('k,'v) map\n\
   end\n\
   end"

let logical_constant ~loc = function
  | S.Pconst_integer (text, suffix) -> Ast_helper.Const.integer ~loc ?suffix text
  | Pconst_char c -> Ast_helper.Const.char ~loc c
  | Pconst_string (text, _) -> Ast_helper.Const.string ~loc text
  | Pconst_float text -> Ast_helper.Const.float ~loc text

let rec logical_pattern (p : S.pat) =
  let loc = p.pat_loc in
  match p.pat_desc with
  | Pwild -> Ast_helper.Pat.any ~loc ()
  | Pid name -> Ast_helper.Pat.var ~loc { txt = name.pid_str; loc }
  | Ptuple pats ->
      Ast_helper.Pat.tuple ~loc
        (List.map pats ~f:(fun p -> (None, logical_pattern p)))
        Closed
  | Pcast (p, typ) ->
      Ast_helper.Pat.constraint_ ~loc (logical_pattern p) (core_type ~at:loc typ)
  | Pconstr (q, arg) ->
      Ast_helper.Pat.construct ~loc
        { txt = longident q; loc }
        (Option.map arg ~f:(fun p -> ([], logical_pattern p)))
  | Pconst c -> Ast_helper.Pat.constant ~loc (logical_constant ~loc c)

let logical_lambda ~loc (id : S.id) typ body =
  let pattern =
    Ast_helper.Pat.var ~loc:id.pid_loc { txt = id.pid_str; loc = id.pid_loc }
  in
  let pattern =
    Option.value_map typ ~default:pattern ~f:(fun typ ->
        Ast_helper.Pat.constraint_ ~loc pattern (core_type ~at:loc typ))
  in
  Ast_helper.Exp.function_ ~loc
    [ { Parsetree.pparam_loc = loc; pparam_desc = Pparam_val (Nolabel, None, pattern) } ]
    None (Pfunction_body body)

let logical_helper ~loc path =
  let path =
    List.fold path ~init:(Longident.Lident "Caravan__logical_check")
      ~f:(fun parent name -> Longident.Ldot ({ txt = parent; loc }, { txt = name; loc }))
  in
  Ast_helper.Exp.ident ~loc { txt = path; loc }

let logical_builtin_path ~functions = function
  | S.Qdot (Qid m, op)
    when List.mem [ "Set"; "Finset"; "Map" ] m.pid_str ~equal:String.equal
         && not (List.mem functions (m.pid_str ^ "." ^ op.pid_str) ~equal:String.equal) ->
      Some [ m.pid_str; op.pid_str ]
  | Qid { pid_str = "to_sequence"; _ }
    when not (List.mem functions "to_sequence" ~equal:String.equal) ->
      Some [ "to_sequence" ]
  | Qid { pid_str = "==="; _ } -> Some [ "equal" ]
  | Qid { pid_str = "=/="; _ } -> Some [ "not_equal" ]
  | Qid { pid_str = "->" | "<->"; _ } -> Some [ "implies" ]
  | _ -> None

let logical_identifier ~functions ~loc q =
  match logical_builtin_path ~functions q with
  | Some path -> logical_helper ~loc path
  | None -> (
      match q with
      | Qid { pid_str = "/\\"; _ } -> Ast_helper.Exp.ident ~loc { txt = Lident "&&"; loc }
      | Qid { pid_str = "\\/"; _ } -> Ast_helper.Exp.ident ~loc { txt = Lident "||"; loc }
      | Qid { pid_str = "-"; pid_fixity = Prefix; _ } ->
          Ast_helper.Exp.ident ~loc { txt = Lident "~-"; loc }
      | _ -> Ast_helper.Exp.ident ~loc { txt = longident q; loc })

let logical_constructor q =
  let last = match q with S.Qid id | Qdot (_, id) -> id.pid_str in
  String.equal last "[]" || String.equal last "::" || String.equal last "()"
  || match String.get last 0 with 'A' .. 'Z' -> true | _ -> false

let rec logical_pattern_names (pattern : S.pat) =
  match pattern.pat_desc with
  | Pid id -> [ id.pid_str ]
  | Ptuple patterns -> List.concat_map patterns ~f:logical_pattern_names
  | Pcast (pattern, _) -> logical_pattern_names pattern
  | Pconstr (_, Some pattern) -> logical_pattern_names pattern
  | Pwild | Pconst _ | Pconstr (_, None) -> []

let shadow_list_projection is_list names =
  let rec shadowed (term : S.term) =
    match term.term_desc with
    | Tvar (Qid id) -> List.mem names id.pid_str ~equal:String.equal
    | Tfield (base, _) -> shadowed base
    | _ -> false
  in
  fun term -> (not (shadowed term)) && is_list term

(** The name under which the type of the field [field] of the record [record], one that no
    OCaml type declares, is known to logical expressions. *)
let record_field record field = record ^ "." ^ field

(** Drops synthetic projections when a lexical binding shadows their record. *)
let shadow_record_projections names variables =
  List.filter variables ~f:(fun (variable, _) ->
      not
        (List.exists names ~f:(fun name -> String.is_prefix variable ~prefix:(name ^ "."))))

let shadow_logical_functions names functions =
  names
  @ List.filter functions ~f:(fun function_ ->
      not
        (List.exists names ~f:(fun name ->
             String.is_prefix function_ ~prefix:(name ^ "."))))

let rec logical_expression ~functions ~is_list (term : S.term) =
  let loc = term.term_loc in
  let exp = logical_expression ~functions ~is_list in
  let apply callee args =
    Ast_helper.Exp.apply ~loc callee
      (List.map args ~f:(fun arg -> (Asttypes.Nolabel, arg)))
  in
  match term.term_desc with
  | Ttrue | Tfalse ->
      Ok
        (Ast_helper.Exp.construct ~loc
           {
             txt = Lident (match term.term_desc with Ttrue -> "true" | _ -> "false");
             loc;
           }
           None)
  | Tconst c -> Ok (Ast_helper.Exp.constant ~loc (logical_constant ~loc c))
  | Tvar q when logical_constructor q ->
      Ok (Ast_helper.Exp.construct ~loc { txt = longident q; loc } None)
  | Tvar q -> Ok (logical_identifier ~functions ~loc q)
  | Tfield ({ term_desc = Tvar (Qid record); _ }, Qid field)
    when List.mem functions
           (record_field record.pid_str field.pid_str)
           ~equal:String.equal ->
      Ok
        (Ast_helper.Exp.ident ~loc
           { txt = Lident (record_field record.pid_str field.pid_str); loc })
  | Tapply
      ( {
          term_desc = Tapply ({ term_desc = Tvar (Qid { pid_str = "::"; _ }); _ }, head);
          _;
        },
        tail ) ->
      let* head = exp head in
      let* tail = exp tail in
      Ok
        (Ast_helper.Exp.construct ~loc { txt = Lident "::"; loc }
           (Some (Ast_helper.Exp.tuple ~loc [ (None, head); (None, tail) ])))
  | Tapply ({ term_desc = Tvar q; _ }, arg) when logical_constructor q ->
      let* arg = exp arg in
      Ok (Ast_helper.Exp.construct ~loc { txt = longident q; loc } (Some arg))
  | Tapply (callee, arg) ->
      let* callee = exp callee in
      let* arg = exp arg in
      Ok (apply callee [ arg ])
  | Tinfix _ -> exp (S.chain term)
  | Tif (condition, yes, no) ->
      let* condition = exp condition in
      let* yes = exp yes in
      let* no = exp no in
      Ok (Ast_helper.Exp.ifthenelse ~loc condition yes (Some no))
  | Tlet (pattern, rhs, body) ->
      let* rhs = exp rhs in
      let is_list = shadow_list_projection is_list (logical_pattern_names pattern) in
      let functions =
        shadow_logical_functions (logical_pattern_names pattern) functions
      in
      let* body = logical_expression ~functions ~is_list body in
      Ok
        (Ast_helper.Exp.let_ ~loc Nonrecursive
           [ Ast_helper.Vb.mk ~loc (logical_pattern pattern) rhs ]
           body)
  | Tmatch (value, cases) ->
      let* value = exp value in
      let* cases =
        Result.all
          (List.map cases ~f:(fun (pattern, body) ->
               let is_list =
                 shadow_list_projection is_list (logical_pattern_names pattern)
               in
               let functions =
                 shadow_logical_functions (logical_pattern_names pattern) functions
               in
               let* body = logical_expression ~functions ~is_list body in
               Ok (Ast_helper.Exp.case (logical_pattern pattern) body)))
      in
      Ok (Ast_helper.Exp.match_ ~loc value cases)
  | Tcast (value, typ) ->
      let* value = exp value in
      Ok (Ast_helper.Exp.constraint_ ~loc value (core_type ~at:loc typ))
  | Ttuple [] -> Ok (Ast_helper.Exp.construct ~loc { txt = Lident "()"; loc } None)
  | Ttuple values ->
      let* values = Result.all (List.map values ~f:exp) in
      Ok (Ast_helper.Exp.tuple ~loc (List.map values ~f:(fun value -> (None, value))))
  | Tquant (_, binders, body) ->
      let names = List.map binders ~f:(fun (id, _) -> id.S.pid_str) in
      let is_list = shadow_list_projection is_list names in
      let functions = shadow_logical_functions names functions in
      let* body = logical_expression ~functions ~is_list body in
      Ok
        (List.fold_right binders ~init:body ~f:(fun (id, typ) body ->
             apply
               (logical_helper ~loc [ "quantify" ])
               [ logical_lambda ~loc id typ body ]))
  | Tcomprehension ((id, typ), body) ->
      let is_list = shadow_list_projection is_list [ id.pid_str ] in
      let functions = shadow_logical_functions [ id.pid_str ] functions in
      let* body = logical_expression ~functions ~is_list body in
      Ok
        (apply
           (logical_helper ~loc [ "Set"; "of_predicate" ])
           [ logical_lambda ~loc id (Some typ) body ])
  | Tfield (base, Qid { pid_str = ("hd" | "tl") as field; _ }) when is_list base ->
      let* base = exp base in
      let id name = S.mk_id ~loc name in
      let callee =
        Ast_helper.Exp.ident ~loc
          { txt = longident (Qdot (Qdot (Qid (id "Stdlib"), id "List"), id field)); loc }
      in
      Ok (apply callee [ base ])
  | Tfield (value, field) ->
      let* value = exp value in
      Ok (Ast_helper.Exp.field ~loc value { txt = longident field; loc })
  | Trecord (base, fields) ->
      let* base =
        match base with
        | None -> Ok None
        | Some base -> Result.map (exp base) ~f:Option.some
      in
      let* fields =
        Result.all
          (List.map fields ~f:(fun (field, value) ->
               Result.map (exp value) ~f:(fun value ->
                   ( {
                       Location.txt = Longident.Lident field.S.pid_str;
                       loc = field.pid_loc;
                     },
                     value ))))
      in
      Ok (Ast_helper.Exp.record ~loc fields base)
  | Tattr (_, value) | Told value -> exp value

(** Types logical expressions before Raven erases reference element types. *)
let typed_logical_expression ?(is_list = fun _ -> false) env ~functions ~variables
    ?expected (term : S.term) =
  try
    let rec free_variables (seen, found) typ =
      let id = Types.get_id typ in
      if Set.mem seen id then (seen, found)
      else
        let seen = Set.add seen id in
        match Types.get_desc typ with
        | Tvar _ when Types.get_level typ = Btype.generic_level -> (seen, typ :: found)
        | _ -> Btype.fold_type_expr free_variables (seen, found) typ
    in
    let _, free =
      List.fold
        (List.map variables ~f:snd @ Option.to_list expected)
        ~init:(Set.empty (module Int), [])
        ~f:free_variables
    in
    let env, substitutions =
      List.fold free ~init:(env, []) ~f:(fun (env, substitutions) variable ->
          let id = Ident.create_local "caravan$logical$type" in
          let declaration = Ctype.new_local_type ~loc:term.term_loc Definition in
          let path = Path.Pident id in
          ( Env.add_type ~check:false id declaration env,
            (variable, path, Ctype.newconstr path []) :: substitutions ))
    in
    (* Generalized source variables are rigid; inference placeholders stay flexible. *)
    let rec freeze typ =
      if List.is_empty substitutions then typ
      else
        match
          List.find substitutions ~f:(fun (variable, _, _) -> Types.eq_type variable typ)
        with
        | Some (_, _, frozen) -> frozen
        | None ->
            begin match Types.get_desc typ with
            | Tvar _ | Tunivar _ -> typ
            | desc -> Ctype.newty (Btype.copy_type_desc freeze desc)
            end
    in
    let rec restore typ =
      match Types.get_desc typ with
      | Tconstr (path, [], _) ->
          begin match
            List.find substitutions ~f:(fun (_, frozen, _) -> Path.same path frozen)
          with
          | Some (variable, _, _) -> variable
          | None -> typ
          end
      | Tvar _ | Tunivar _ -> typ
      | desc -> Ctype.newty (Btype.copy_type_desc restore desc)
    in
    let variables = List.map variables ~f:(fun (name, typ) -> (name, freeze typ)) in
    let expected = Option.map expected ~f:freeze in
    let functions = List.map variables ~f:fst @ functions in
    let* expression = logical_expression ~functions ~is_list term in
    let env =
      (Typemod.type_interface env
         (Parse.interface (Lexing.from_string logical_check_signature)))
        .sig_final_env
    in
    let add env name typ =
      Env.add_value (Ident.create_local name)
        {
          Types.val_type = typ;
          val_kind = Val_reg;
          val_loc = term.term_loc;
          val_attributes = [];
          val_uid = Shape.Uid.internal_not_actually_unique;
        }
        env
    in
    let env =
      List.fold_right variables ~init:env ~f:(fun (name, typ) env -> add env name typ)
    in
    let env, expression =
      match expected with
      | None -> (env, expression)
      | Some expected ->
          let name = "caravan$logical$expected" in
          let argument =
            match Types.get_desc expected with
            | Tpoly _ -> expected
            | _ -> Btype.newgenty (Tpoly (expected, []))
          in
          let expected =
            Ctype.newty (Tarrow (Nolabel, argument, Predef.type_unit, Types.commu_ok))
          in
          let env = add env name expected in
          let application =
            Ast_helper.Exp.apply ~loc:term.term_loc
              (Ast_helper.Exp.ident ~loc:term.term_loc
                 { txt = Lident name; loc = term.term_loc })
              [ (Nolabel, expression) ]
          in
          (env, application)
    in
    let typed = Typecore.type_expression env expression in
    let partial_match = ref None in
    let default = Tast_iterator.default_iterator in
    let iterator =
      {
        default with
        expr =
          (fun self expression ->
            begin match (expression.Typedtree.exp_desc, !partial_match) with
            | Texp_match (_, _, _, Partial), None ->
                partial_match := Some expression.exp_loc
            | _ -> ()
            end;
            default.expr self expression);
      }
    in
    iterator.expr iterator typed;
    match !partial_match with
    | None when List.is_empty substitutions -> Ok typed
    | None ->
        let mapper =
          {
            Tast_mapper.default with
            expr =
              (fun self expression ->
                let expression = Tast_mapper.default.expr self expression in
                { expression with exp_type = restore expression.exp_type });
          }
        in
        Ok (mapper.expr mapper typed)
    | Some at -> Error (Report.error Type at "A logical match must be exhaustive")
  with exn -> (
    match Report.of_exn exn with
    | Some error -> Error error
    | None -> Error (Report.error Type term.term_loc (Stdlib.Printexc.to_string exn)))

let type_logical_expression ?is_list env ~functions ~variables ?expected term =
  Result.map (typed_logical_expression ?is_list env ~functions ~variables ?expected term)
    ~f:(fun expression -> expression.Typedtree.exp_type)

let infer_typed_logical_expression ?is_list env ~functions ~variables term =
  typed_logical_expression ?is_list env ~functions ~variables term

let infer_logical_expression ?is_list env ~functions ~variables term :
    (Types.type_expr, Report.error) Result.t =
  type_logical_expression ?is_list env ~functions ~variables term

let check_logical_expression ?is_list env ~functions ~variables ~expected term =
  Result.map (type_logical_expression ?is_list env ~functions ~variables ~expected term)
    ~f:(fun _ -> ())

let check_logical_function env ~functions = function
  | S.Proof_function { function_params; function_result; function_body; function_name } ->
      let* variables =
        Result.all
          (List.map function_params ~f:(fun ((id : S.id), typ) ->
               let* typ = ocaml_type env ~at:id.pid_loc typ in
               Ok (id.pid_str, typ)))
      in
      let* expected = ocaml_type env ~at:function_name.pid_loc function_result in
      check_logical_expression env ~functions ~variables ~expected function_body
  | _ -> Ok ()

(** Compiler paths retain the identity selected by lexical module aliases. *)
let normalize_value_path env ~at path =
  try Ok (Env.normalize_value_path (Some at) env path)
  with exn -> (
    match Report.of_exn exn with
    | Some error -> Error error
    | None -> Error (Report.error Type at (Stdlib.Printexc.to_string exn)))

let value_path env q =
  try
    let path, _ = Env.find_value_by_name (longident q) env in
    Some (Env.normalize_value_path None env path)
  with Stdlib.Not_found -> None

let module_path env q =
  try
    let path, _ = Env.find_module_by_name (longident q) env in
    Some (Env.normalize_module_path None env path)
  with Stdlib.Not_found -> None

let constructor env q =
  try Some (Env.find_constructor_by_name (longident q) env)
  with Stdlib.Not_found -> None
