(** What loading a source and typing its proofs share: the records of a source, and the
    lookups of its names and types. *)

open Base
module S = Caravan_spec.Spec_ast

let ( let* ) = Result.( >>= )

type interface = {
  signature : Parsetree.signature;
  typed_signature : Typedtree.signature option;
  interface_comments : (string * Location.t) list;
  scope : Declaration_scope.t;
}

type library_proof = {
  proof_module : string;
  proof_owner : Path.t option;
  proof_file : string;
  proof_text : string;
  proof_declarations : S.proof_decl list;
  proof_checked : bool;
}

type library = {
  library_name : string;
  library_id : Ident.t;
  library : interface;
  library_proof : library_proof option;
}
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
  resource_parameters : Types.type_expr list;
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
  field_parameters : Types.type_expr list;
  field_family : string option;
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
  au_parameters : Types.type_expr list;
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
  outline_annotations : Annotation.t list;
      (** The annotations that the proof outlines of the [.proof] file stand for. *)
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

let library_proof_for_owner source owner =
  Option.bind owner ~f:(fun owner ->
      List.find_map source.libraries ~f:(fun library ->
          Option.bind library.library_proof ~f:(fun proof ->
              Option.some_if
                (Option.exists proof.proof_owner ~f:(Path.same owner))
                (library, proof))))

let trusted_proof source owner =
  Option.exists (library_proof_for_owner source owner) ~f:(fun (_, proof) ->
      not proof.proof_checked)

let library_model source path =
  List.find_map source.libraries ~f:(fun library ->
      if Path.same path (Path.Pident library.library_id) then
        Option.bind library.library_proof ~f:(fun proof -> proof.proof_owner)
      else None)

(** The annotations of the implementation: its own, or those of its proof outlines. *)
let annotations source =
  Annotation.of_comments source.comments @ source.outline_annotations

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

let find_type_by_name env name =
  try Some (Env.find_type_by_name (Lident name) env) with Stdlib.Not_found -> None

let find_constructor_by_name env name =
  try Some (Env.find_constructor_by_name (Lident name) env)
  with Stdlib.Not_found -> None
