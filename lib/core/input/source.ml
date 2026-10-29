(** An OCaml implementation, parsed and type-checked by the compiler's own front end, with
    its interface and proof, if there are any: [f.mli] and [f.proof] next to [f.ml]. *)

open Base
module S = Caravan_spec.Spec_ast

let ( let* ) = Result.( >>= )

type interface = {
  signature : Parsetree.signature;
  typed_signature : Typedtree.signature option;
  interface_comments : (string * Location.t) list;
  scope : Declaration_scope.t;
}

type library = { library_name : string; library_id : Ident.t; library : interface }
(** A library that the file uses, which an interface [m.mli] without an implementation
    next to it declares: the module [M], trusted. *)

type proof_module_argument =
  | Type_argument of Types.type_expr
  | Module_argument of Path.t

type proof_resource = {
  resource_name : string;
  resource_backend : string;
  resource_scope : Path.t option;
  resource_path : Path.t;
  resource_environment : Env.t;
  resource_functor : string list;
  resource_arguments : proof_module_argument list;
  resource_is_ra : bool;
  resource_interfaces : string list list;
  resource_alias_of : Path.t option;
  resource_definition : bool;
  resource_abstract : bool;
  resource_representation : Types.type_expr option;
  resource_type_members : (string * Ident.t * Types.type_declaration) list;
  resource_type : Types.type_expr;
  resource_id : Ident.t;
  resource_operations : (string * Types.type_expr list * Types.type_expr) list;
  resource_constants : string list;
  resource_descriptor : Datatypes.t;
  resource_aliases : Datatypes.t list;
  resource_at : Location.t;
  resource_public : proof_resource option;
  resource_application : (Path.t * Ident.t) option;
}

let resource_has_path resource path =
  Path.same path resource.resource_path
  || Path.same path (Path.Pident resource.resource_id)
  || Option.exists resource.resource_application ~f:(fun (identity, _) ->
      Path.same path (Path.Pdot (identity, resource.resource_name)))

type proof_field = {
  field_name : string;
  field_backend : string;
  field_scope : Path.t option;
  field_id : Ident.t;
  field_path : Path.t;
  field_environment : Env.t;
  field_owner : Types.type_expr;
  field_value : Types.type_expr;
  field_resource : Path.t option;
  field_at : Location.t;
}

type proof_au = {
  au_name : string;
  au_scope : Path.t option;
  au_id : Ident.t;
  au_path : Path.t;
  au_environment : Env.t;
  au_operation : S.qualid;
  au_operation_path : Path.t;
  au_operation_type : Types.type_expr;
  au_token : Types.type_expr;
  au_token_path : Path.t;
  au_token_paths : Path.t list;
  au_at : Location.t;
  au_application : (Path.t * Ident.t) option;
}

let au_has_path au path =
  Path.same path au.au_path
  || Path.same path (Path.Pident au.au_id)
  || Option.exists au.au_application ~f:(fun (identity, _) ->
      Path.same path (Path.Pdot (identity, au.au_name)))
  || List.exists au.au_token_paths ~f:(function
    | Path.Pdot (owner, "token") -> Path.same path owner
    | Pident _ | Pdot _ | Papply _ | Pextra_ty _ -> false)

type t = {
  file : string;
  text : string;
  scope : Declaration_scope.t;
  typed : Typedtree.structure;
  comments : (string * Location.t) list;  (** With their text, without delimiters. *)
  env : Env.t;
      (** The environment at the end of the file, for types in annotations, with the type
          [integer], [sequence], [finset], [set], and [map] of specifications. *)
  sequence : Path.t;  (** The type ['a sequence] of specifications. *)
  logical_types : Datatypes.t list;
      (** The logical types of specifications, identified by their declarations. *)
  proof_types : Datatypes.t list;  (** Algebraic types declared by the proof. *)
  proof_resources : proof_resource list;
  signature_resources : (Location.t * proof_resource) list;
  proof_fields : proof_field list;
  proof_aus : proof_au list;
  proof_applications : Functor_context.application list;
  pending : Path.t;
      (** The type ['k pending] of specifications: calls of an operation waiting to be
          helped, each on a key. *)
  interface : interface option;
  proof : S.proof_decl list;  (** The declarations of the proof. *)
  proof_scopes : Proof_scopes.t;
  libraries : library list;
  spec_bindings : Types.signature;
}

(** The specification declarations added after the runtime program was typed. *)
let specification_bindings runtime_env env =
  let boundary = Env.summary runtime_env in
  let rec collect seen bindings summary =
    if phys_equal summary boundary then bindings
    else
      let binding previous id declaration =
        if List.mem seen id ~equal:Ident.same then collect seen bindings previous
        else collect (id :: seen) (declaration :: bindings) previous
      in
      match summary with
      | Env.Env_empty -> bindings
      | Env_value (previous, id, declaration) ->
          binding previous id (Types.Sig_value (id, declaration, Exported))
      | Env_type (previous, id, declaration) ->
          binding previous id (Types.Sig_type (id, declaration, Trec_not, Exported))
      | Env_module (previous, id, presence, declaration) ->
          binding previous id
            (Types.Sig_module (id, presence, declaration, Trec_not, Exported))
      | Env_modtype (previous, id, declaration) ->
          binding previous id (Types.Sig_modtype (id, declaration, Exported))
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
          collect seen bindings previous
  in
  collect [] [] (Env.summary env)

(** Adds the shared specification identities without hiding lexical runtime names. *)
let source_module_ids (structure : Typedtree.structure) =
  List.concat_map structure.str_items ~f:(fun item ->
      match item.str_desc with
      | Tstr_module { mb_id = Some id; _ } -> [ id ]
      | Tstr_recmodule declarations ->
          List.filter_map declarations ~f:(fun declaration -> declaration.mb_id)
      | _ -> [])

let source_type_ids (structure : Typedtree.structure) =
  List.concat_map structure.str_items ~f:(fun item ->
      match item.str_desc with
      | Tstr_type (_, declarations) ->
          List.map declarations ~f:(fun declaration ->
              (declaration.typ_id, declaration.typ_name.txt))
      | _ -> [])

let scoped_value_name (scope : Proof_scopes.scope) path =
  let values =
    List.concat_map scope.structure.str_items ~f:(fun item ->
        match item.str_desc with
        | Tstr_value (_, bindings) ->
            List.filter_map bindings ~f:(fun binding ->
                match binding.vb_pat.pat_desc with
                | Tpat_var (id, _, _) -> Some (id, Ident.name id)
                | _ -> None)
        | _ -> [])
  in
  match path with
  | Path.Pident id -> List.Assoc.find values id ~equal:Ident.same
  | Pdot (owner, name)
    when Option.exists scope.owner ~f:(Path.same owner)
         && List.exists values ~f:(fun (_, member) -> String.equal member name) ->
      Some name
  | Pdot _ | Papply _ | Pextra_ty _ -> None

let add_spec_bindings ?(source_modules = []) spec_bindings lexical_env =
  let find lookup id =
    try Some (lookup (Longident.Lident (Ident.name id)) lexical_env)
    with Stdlib.Not_found -> None
  in
  List.fold spec_bindings ~init:lexical_env ~f:(fun env -> function
    | Types.Sig_type (id, declaration, _, _) ->
        begin match find Env.find_type_by_name id with
        | None -> Env.add_type ~check:false id declaration env
        | Some (Pident local, declaration') ->
            Env.add_type ~check:false local declaration'
              (Env.add_type ~check:false id declaration env)
        | Some ((Pdot _ | Papply _ | Pextra_ty _), _) -> env
        end
    | Sig_value (id, declaration, _) ->
        begin match find Env.find_value_by_name id with
        | None -> Env.add_value id declaration env
        | Some (Pident local, declaration') ->
            Env.add_value local declaration' (Env.add_value id declaration env)
        | Some ((Pdot _ | Papply _ | Pextra_ty _), _) -> env
        end
    | Sig_module (id, presence, declaration, _, _) ->
        let lexical = find Env.find_module_by_name id in
        let visible =
          (not (List.mem source_modules id ~equal:Ident.same))
          || Option.exists lexical ~f:(function
            | Pident local, _ -> Ident.same local id
            | _ -> false)
        in
        if not visible then env
        else
          begin match lexical with
          | None -> Env.add_module_declaration ~check:false id presence declaration env
          | Some (Pident local, declaration') ->
              let declaration' =
                if Ident.same local id then declaration else declaration'
              in
              Env.add_module_declaration ~check:false local Mp_present declaration'
                (Env.add_module_declaration ~check:false id presence declaration env)
          | Some ((Pdot _ | Papply _ | Pextra_ty _), _) -> env
          end
    | Sig_modtype (id, declaration, _) ->
        begin match find Env.find_modtype_by_name id with
        | None -> Env.add_modtype id declaration env
        | Some (Pident local, declaration') ->
            Env.add_modtype local declaration' (Env.add_modtype id declaration env)
        | Some ((Pdot _ | Papply _ | Pextra_ty _), _) -> env
        end
    | Sig_typext _ | Sig_class _ | Sig_class_type _ -> env)

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
let load_proof file : (S.proof_decl list, Report.error) Result.t =
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

let rec longident : S.qualid -> Longident.t = function
  | Qid id -> Lident id.pid_str
  | Qdot (q, id) ->
      Ldot
        ( { txt = longident q; loc = S.qualid_loc q },
          { txt = id.pid_str; loc = id.pid_loc } )

let rec core_type ~(at : Location.t) (t : S.pty) : Parsetree.core_type =
  match t with
  | PTtyvar id -> Ast_helper.Typ.var ~loc:id.pid_loc id.pid_str
  | PTtyapp (q, args) ->
      let loc = S.qualid_loc q in
      Ast_helper.Typ.constr ~loc
        { txt = longident q; loc }
        (List.map args ~f:(core_type ~at))
  | PTtuple ts ->
      Ast_helper.Typ.tuple ~loc:at (List.map ts ~f:(fun t -> (None, core_type ~at t)))
  | PTarrow (a, b) ->
      Ast_helper.Typ.arrow ~loc:at Nolabel (core_type ~at a) (core_type ~at b)

let rec monotype typ =
  match Types.get_desc typ with Tpoly (body, []) -> monotype body | _ -> typ

let rec function_arguments typ =
  let typ = monotype typ in
  match Types.get_desc typ with
  | Tarrow (_, argument, rest, _) ->
      let arguments, result = function_arguments rest in
      (monotype argument :: arguments, result)
  | _ -> ([], typ)

let find_type_by_name env name =
  try Some (Env.find_type_by_name (Lident name) env) with Stdlib.Not_found -> None

let find_constructor_by_name env name =
  try Some (Env.find_constructor_by_name (Lident name) env)
  with Stdlib.Not_found -> None

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
      | S.Proof_type { type_ctors; _ } -> List.map type_ctors ~f:fst
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
  let checked_type env at typ =
    (Typetexp.transl_simple_type env ~closed:true (core_type ~at typ)).ctyp_type
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
        | S.Proof_type { type_name; type_ctors } ->
            let constructor ((name : S.id), (args : S.pty list)) =
              Ast_helper.Type.constructor ~loc:name.pid_loc
                ~args:(Pcstr_tuple (List.map args ~f:(core_type ~at:name.pid_loc)))
                { txt = name.pid_str; loc = name.pid_loc }
            in
            let declaration =
              Ast_helper.Type.mk ~loc:type_name.pid_loc
                ~kind:(Ptype_variant (List.map type_ctors ~f:constructor))
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
              Result.all (List.map typed_declarations ~f:Datatypes.of_declaration)
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
            let declaration =
              Ast_helper.Sig.module_
                (Ast_helper.Md.mk ~loc:at
                   { txt = Some name.pid_str; loc = at }
                   (Ast_helper.Mty.signature ~loc:at
                      [
                        Ast_helper.Sig.type_ Nonrecursive
                          [ Ast_helper.Type.mk ~loc:at { txt = "token"; loc = at } ];
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
            let token = Ctype.newconstr token_path [] in
            let arrow args result =
              List.fold_right args ~init:result ~f:(fun arg result ->
                  Ctype.newty (Tarrow (Nolabel, arg, result, Types.commu_ok)))
            in
            let value (name, args, result) =
              let id = Ident.create_local name in
              Types.Sig_value
                ( id,
                  {
                    val_type = arrow args result;
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
                         | S.Proof_type_argument typ ->
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
                             Ok (Type_argument (checked_type env at typ))
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
                             Ok (Module_argument path)))
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
                            && same_arguments left.resource_arguments
                                 right.resource_arguments
                        end
                and same_arguments left right =
                  List.length left = List.length right
                  && List.for_all2_exn left right ~f:(fun left right ->
                      match (left, right) with
                      | Type_argument left, Type_argument right ->
                          Ctype.is_equal env false [ left ] [ right ]
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
                in
                let applicative_source =
                  List.find resources ~f:(fun resource ->
                      Option.is_none resource.resource_alias_of
                      && (not resource.resource_definition)
                      && (not resource.resource_abstract)
                      && List.equal String.equal resource.resource_functor library.path
                      && same_arguments resource.resource_arguments arguments)
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
                                Ast_helper.Type.mk ~loc:at
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
                      | S.Proof_type_argument typ ->
                          Some (parameter.name, alias_name parameter, typ)
                      | Proof_module_argument _ -> None)
                in
                let named name =
                  Ast_helper.Typ.constr ~loc:at { txt = Lident name; loc = at } []
                in
                let substitutions =
                  List.map pairs ~f:(fun (formal, argument) ->
                      let typ =
                        match argument with
                        | S.Proof_type_argument _ -> named (alias_name formal)
                        | Proof_module_argument q ->
                            Ast_helper.Typ.constr ~loc:at
                              {
                                txt =
                                  Ldot
                                    ( { txt = longident q; loc = at },
                                      { txt = "t"; loc = at } );
                                loc = at;
                              }
                              []
                      in
                      (formal.name, typ))
                in
                let metadata_type =
                  Proof_library.ocaml_type ~at ~signature:library ~substitutions
                in
                let operation_type =
                  Proof_library.operation_type ~at ~signature:library ~substitutions
                in
                let* type_items =
                  Result.all
                    (List.map library_types ~f:(fun member ->
                         let* manifest =
                           match
                             List.find type_members ~f:(fun (name, _, _) ->
                                 String.equal name member.name)
                           with
                           | Some (_, id, _) -> Ok (Some (named (Ident.name id)))
                           | None when Option.is_some member.definition && not member.rep
                             ->
                               let definition = Option.value_exn member.definition in
                               let* typ = metadata_type definition in
                               Ok (Some typ)
                           | _ -> Ok None
                         in
                         let declaration =
                           Ast_helper.Type.mk ~loc:at ?manifest
                             { txt = String.uncapitalize member.name; loc = at }
                         in
                         Ok (Ast_helper.Sig.type_ Nonrecursive [ declaration ])))
                in
                let alias_items =
                  List.map alias_names ~f:(fun (_, alias, typ) ->
                      Ast_helper.Sig.type_ Nonrecursive
                        [
                          Ast_helper.Type.mk ~loc:at ~manifest:(core_type ~at typ)
                            { txt = alias; loc = at };
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
                               Proof_library.operation_type ~at ~signature:selected
                                 ~substitutions:[] inherited
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
                                 Proof_library.ocaml_type ~at ~signature:selected
                                   ~substitutions:[] inherited
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
                  checked_type env at (PTtyapp (Qdot (Qid name, S.mk_id ~loc:at "t"), []))
                in
                let resource_descriptor =
                  let descriptor =
                    Datatypes.resource_type ~name:name.pid_str ~module_id:resource_id ~at
                  in
                  let paths =
                    List.filter_map type_members ~f:(fun (member, id, _) ->
                        Option.some_if (String.equal member "T") (Path.Pident id))
                  in
                  let descriptor = Datatypes.with_paths descriptor paths in
                  Option.value_map applicative_source ~default:descriptor
                    ~f:(fun previous ->
                      { descriptor with alias = Some previous.resource_type })
                in
                let resource_aliases =
                  List.map alias_names ~f:(fun (_, alias, typ) ->
                      {
                        (Datatypes.library_type ~library:name.pid_str
                           ~library_id:resource_id ~at alias)
                        with
                        alias = Some (checked_type env at typ);
                      })
                in
                let value_type operation =
                  let qualified =
                    Longident.Ldot
                      ( { txt = Longident.Lident name.pid_str; loc = at },
                        { txt = operation; loc = at } )
                  in
                  let _, value = Env.find_value_by_name qualified env in
                  let inputs, output = function_arguments value.Types.val_type in
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
            let* owner, content =
              match field_type with
              | PTtyapp (Qdot (Qid ghost, field), [ owner; content ])
                when String.equal ghost.pid_str "Ghost"
                     && String.equal field.pid_str "field" ->
                  Ok (checked_type env at owner, checked_type env at content)
              | _ ->
                  Error
                    (Report.error Type at
                       "A ghost field requires an (owner, value) Ghost.field type")
            in
            let owner_head = Ctype.expand_head env owner in
            let owner_is_reference =
              match Types.get_desc owner_head with
              | Tconstr (p, [ _ ], _) when Datatypes.is_atomic p || Datatypes.is_ref p ->
                  true
              | Tconstr (p, [], _) when Datatypes.is_ghost p -> true
              | Tconstr (p, [], _) ->
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
              | Tconstr (Pdot (module_path, "t"), [], _) ->
                  let canonical =
                    Env.normalize_module_path None env module_path |> canonical_owner
                  in
                  Option.bind
                    (Option.first_some
                       (resource_at_path env resources module_path)
                       (resource_at_path env resources canonical))
                    ~f:(fun resource ->
                      Option.some_if resource.resource_is_ra
                        (Path.Pident resource.resource_id))
              | _ -> None
            in
            let* env = value env name (core_type ~at field_type) in
            let field_path, _ = Env.find_value_by_name (Lident name.pid_str) env in
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
                  let descriptor =
                    Datatypes.resource_type ~name:original.resource_name ~module_id:id
                      ~at:original.resource_at
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
                        | Type_argument typ ->
                            Type_argument (Subst.type_expr substitution typ)
                        | Module_argument path ->
                            Module_argument (Subst.module_path substitution path));
                    resource_alias_of =
                      Option.map original.resource_alias_of
                        ~f:(Subst.module_path substitution);
                    resource_type_members = [];
                    resource_type = Ctype.newconstr (Path.Pdot (path, "t")) [];
                    resource_id = id;
                    resource_operations =
                      List.map original.resource_operations
                        ~f:(fun (name, inputs, output) ->
                          ( name,
                            List.map inputs ~f:(Subst.type_expr substitution),
                            Subst.type_expr substitution output ));
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
                            alias =
                              Option.map alias.alias ~f:(Subst.type_expr substitution);
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
                {
                  au with
                  au_scope = None;
                  au_id = Ident.create_local au.au_name;
                  au_path = path;
                  au_environment = qualified_env;
                  au_operation_path = operation_path;
                  au_operation_type = Subst.type_expr substitution au.au_operation_type;
                  au_token = Ctype.newconstr token_path [];
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
    let proof = Option.value_map (sibling file ".proof") ~default:(Ok []) ~f:load_proof in
    Result.bind proof ~f:(fun proof ->
        let* env, _, _, _, _ = elaborate_proof_types env interface [] in
        let* signature_resources = signature_ghost_resources env signature_comments in
        let* env, imported_resources = imported_proof_resources env libraries in
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
            elaborate_proof_types ~add_standard:false ~allow_interfaces:true
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
                     scoped_proof_types ~applications ~only:[ module_name.pid_str ]
                       ?public_interface:interface ~comments:signature_comments
                       ~previous_resources:resources runtime_env env proof_scopes
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
                     scoped_proof_types ~applications ~only:[ module_name.pid_str ]
                       ?public_interface:interface ~comments:signature_comments
                       ~previous_resources:resources runtime_env env proof_scopes
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
                     elaborate_proof_types ~add_standard:false
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
              implicit_ghost_scopes ~comments:signature_comments proof_scopes
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
                  scoped_proof_types ~applications
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
      let functions = logical_pattern_names pattern @ functions in
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
               let functions = logical_pattern_names pattern @ functions in
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
      let functions = names @ functions in
      let* body = logical_expression ~functions ~is_list body in
      Ok
        (List.fold_right binders ~init:body ~f:(fun (id, typ) body ->
             apply
               (logical_helper ~loc [ "quantify" ])
               [ logical_lambda ~loc id typ body ]))
  | Tcomprehension ((id, typ), body) ->
      let is_list = shadow_list_projection is_list [ id.pid_str ] in
      let functions = id.pid_str :: functions in
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
  | Tattr (_, value) | Told value -> exp value

(** Types logical expressions before Raven erases reference element types. *)
let type_logical_expression ?(is_list = fun _ -> false) env ~functions ~variables
    ?expected (term : S.term) =
  try
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
    | None -> Ok typed.exp_type
    | Some at -> Error (Report.error Type at "A logical match must be exhaustive")
  with exn -> (
    match Report.of_exn exn with
    | Some error -> Error error
    | None -> Error (Report.error Type term.term_loc (Stdlib.Printexc.to_string exn)))

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
