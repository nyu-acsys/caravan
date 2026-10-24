(** An OCaml implementation, parsed and type-checked by the compiler's own front end, with
    its interface and proof, if there are any: [f.mli] and [f.proof] next to [f.ml]. *)

open Base
module S = Caravan_spec.Spec_ast

let ( let* ) = Result.( >>= )

type interface = {
  signature : Parsetree.signature;
  interface_comments : (string * Location.t) list;
  scope : Declaration_scope.t;
}

type library = { library_name : string; library_id : Ident.t; library : interface }
(** A library that the file uses, which an interface [m.mli] without an implementation
    next to it declares: the module [M], trusted. *)

type proof_resource = {
  resource_name : string;
  resource_kind : S.resource_kind;
  resource_type : Types.type_expr;
  resource_id : Ident.t;
  resource_operations : (string * Types.type_expr list * Types.type_expr) list;
  resource_descriptor : Datatypes.t;
  resource_aliases : Datatypes.t list;
  resource_at : Location.t;
}

type proof_field = {
  field_name : string;
  field_owner : Types.type_expr;
  field_value : Types.type_expr;
  field_at : Location.t;
}

type proof_au = {
  au_name : string;
  au_operation : S.qualid;
  au_operation_path : Path.t;
  au_operation_type : Types.type_expr;
  au_token : Types.type_expr;
  au_token_path : Path.t;
  au_at : Location.t;
}

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
  proof_fields : proof_field list;
  proof_aus : proof_au list;
  pending : Path.t;
      (** The type ['k pending] of specifications: calls of an operation waiting to be
          helped, each on a key. *)
  interface : interface option;
  proof : S.proof_decl list;  (** The declarations of the proof. *)
  libraries : library list;
}

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
    interface_comments = Lexer.comments ();
    scope = Declaration_scope.of_lexbuf ~file lexbuf;
  }

(** Uses OCaml's inclusion checker before specializing the implementation. *)
let check_interface env signature interface =
  try
    let declared = Typemod.type_interface env interface.signature in
    Includemod.check_implementation env signature declared.sig_type;
    Ok ()
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
let specialize_to_interface env (typed : Typedtree.structure) (interface : interface) =
  let declared =
    List.filter_map interface.signature ~f:(fun item ->
        match item.psig_desc with
        | Psig_value vd -> Some (vd.pval_name.txt, vd.pval_type)
        | _ -> None)
  in
  List.iter typed.str_items ~f:(fun item ->
      match item.str_desc with
      | Tstr_value (_, bindings) ->
          List.iter bindings ~f:(fun (vb : Typedtree.value_binding) ->
              match vb.vb_pat.pat_desc with
              | Tpat_var (id, _, _) ->
                  begin match
                    List.Assoc.find declared (Ident.name id) ~equal:String.equal
                  with
                  | Some ct ->
                      let iface =
                        (Typetexp.transl_simple_type env ~closed:false ct).ctyp_type
                      in
                      specialize env vb.vb_expr.exp_type iface
                  | None -> ()
                  end
              | _ -> ())
      | _ -> ())

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

let proof_type_collision env interface proof =
  let declared =
    List.map (interface_type_declarations interface) ~f:(fun d -> d.ptype_name.txt)
  in
  let rec find seen = function
    | [] -> None
    | S.Proof_type { type_name; _ } :: rest ->
        if
          List.mem seen type_name.pid_str ~equal:String.equal
          || List.mem declared type_name.pid_str ~equal:String.equal
          || Option.is_some (find_type_by_name env type_name.pid_str)
        then Some type_name
        else find (type_name.pid_str :: seen) rest
    | _ :: rest -> find seen rest
  in
  find [] proof

let proof_constructor_collision env interface proof =
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
          || Option.is_some (find_constructor_by_name env name.pid_str)
        then Some name
        else find (name.pid_str :: seen) rest
  in
  find [] constructors

(** Type-checks the algebraic types of [proof] in [env], after the implementation, and
    returns their descriptors and the environment for the rest of the proof. *)
let elaborate_proof_types (env : Env.t) (interface : interface option)
    (proof : S.proof_decl list) :
    ( Env.t * Datatypes.t list * proof_resource list * proof_field list * proof_au list,
      Report.error )
    Result.t =
  let* () =
    match proof_type_collision env interface proof with
    | None -> Ok ()
    | Some name ->
        Error
          (Report.error Type name.pid_loc
             (Printf.sprintf "The proof type %s is already declared" name.pid_str))
  in
  let* () =
    match proof_constructor_collision env interface proof with
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
    if value_exists env name.pid_str then
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
  let* () = reserve_module env "Ghost" in
  let* () = reserve_module env "Permission" in
  let env =
    signature env
      (Parse.interface
         (Lexing.from_string "module Ghost : sig type t type ('owner, 'value) field end"))
  in
  let env =
    signature env
      (Parse.interface
         (Lexing.from_string
            "module Permission : sig type t val half : t val full : t end"))
  in
  let aus = ref [] in
  let* env, reversed, resources, fields =
    List.fold_result proof ~init:(env, [], [], [])
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
                Ok (path, value.Types.val_type)
              with Stdlib.Not_found ->
                Error
                  (Report.error Type (S.qualid_loc operation)
                     "The AU operation is not an OCaml function")
            in
            let rec arguments typ =
              match Types.get_desc typ with
              | Tpoly (body, []) -> arguments body
              | Tarrow (_, argument, rest, _) ->
                  let args, result = arguments rest in
                  (argument :: args, result)
              | _ -> ([], typ)
            in
            let args, result = arguments operation_type in
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
                au_operation = operation;
                au_operation_path = operation_path;
                au_operation_type = operation_type;
                au_token = token;
                au_token_path = token_path;
                au_at = at;
              }
              :: !aus;
            Ok (env, descriptors, resources, fields)
        | Proof_resource { resource_name = name; resource_kind } ->
            let at = name.pid_loc in
            let* () =
              if
                module_exists env name.pid_str
                || Option.is_some
                     (find_type_by_name env (String.uncapitalize name.pid_str))
                || List.exists proof ~f:(function
                  | S.Proof_type { type_name; _ } ->
                      String.equal (String.capitalize type_name.pid_str) name.pid_str
                  | _ -> false)
                || List.mem
                     [ "Ghost"; "Permission"; "SetRA"; "Auth"; "Finset" ]
                     name.pid_str ~equal:String.equal
              then
                Error
                  (Report.error Type at
                     (Printf.sprintf "The proof module %s is already declared or reserved"
                        name.pid_str))
              else Ok ()
            in
            let element_type =
              match resource_kind with
              | Resource_set elt -> Some (checked_type env at elt)
              | Resource_auth _ -> None
            in
            let named name =
              Ast_helper.Typ.constr ~loc:at { txt = Longident.Lident name; loc = at } []
            in
            let t = named "t" in
            let arrow a b = Ast_helper.Typ.arrow ~loc:at Nolabel a b in
            let* extra_types, extra =
              match resource_kind with
              | Resource_set elt ->
                  let _ = checked_type env at elt in
                  let set =
                    Ast_helper.Typ.constr ~loc:at
                      { txt = Lident "set"; loc = at }
                      [ named "element" ]
                  in
                  Ok
                    ( [
                        Ast_helper.Sig.type_ Nonrecursive
                          [
                            Ast_helper.Type.mk ~loc:at ~manifest:(core_type ~at elt)
                              { txt = "element"; loc = at };
                          ];
                      ],
                      [ ("set", arrow set t) ] )
              | Resource_auth underlying ->
                  begin match
                    List.find resources ~f:(fun r ->
                        String.equal r.resource_name underlying.pid_str)
                  with
                  | None ->
                      Error
                        (Report.error Type underlying.pid_loc
                           "Auth requires a previously declared resource module")
                  | Some _ ->
                      let base =
                        Ast_helper.Typ.constr ~loc:at
                          {
                            txt =
                              Ldot
                                ( { txt = Lident underlying.pid_str; loc = at },
                                  { txt = "t"; loc = at } );
                            loc = at;
                          }
                          []
                      in
                      Ok
                        ( [],
                          ("auth_frag", arrow base (arrow base t))
                          :: List.map [ "auth"; "frag"; "full" ] ~f:(fun n ->
                              (n, arrow base t)) )
                  end
            in
            let values =
              extra
              @ [
                  ("id", t);
                  ("top", t);
                  ("valid", arrow t (named "bool"));
                  ("comp", arrow t (arrow t t));
                  ("frame", arrow t (arrow t t));
                  ("fpuAllowed", arrow t (arrow t (named "bool")));
                ]
            in
            let declaration =
              Ast_helper.Sig.module_
                (Ast_helper.Md.mk ~loc:at
                   { txt = Some name.pid_str; loc = at }
                   (Ast_helper.Mty.signature ~loc:at
                      (extra_types
                      @ [
                          Ast_helper.Sig.type_ Recursive
                            [ Ast_helper.Type.mk ~loc:at { txt = "t"; loc = at } ];
                        ]
                      @ List.map values ~f:(fun (n, typ) ->
                          Ast_helper.Sig.value
                            (Ast_helper.Val.mk ~loc:at { txt = n; loc = at } typ)))))
            in
            let typed = Typemod.type_interface env [ declaration ] in
            let env = typed.sig_final_env in
            let path, _ = Env.find_module_by_name (Lident name.pid_str) env in
            let* resource_id =
              match path with
              | Pident id -> Ok id
              | _ ->
                  Error (Report.error Type at "A proof resource must be a local module")
            in
            let resource_type =
              checked_type env at (PTtyapp (Qdot (Qid name, S.mk_id ~loc:at "t"), []))
            in
            let resource_descriptor =
              Datatypes.resource_type ~name:name.pid_str ~module_id:resource_id ~at
            in
            let resource_aliases =
              Option.to_list
                (Option.map element_type ~f:(fun typ ->
                     {
                       (Datatypes.library_type ~library:name.pid_str
                          ~library_id:resource_id ~at "element")
                       with
                       alias = Some typ;
                     }))
            in
            let* specific_operations =
              match (resource_kind, element_type) with
              | Resource_set _, Some element ->
                  let path, _ = Env.find_type_by_name (Lident "set") env in
                  Ok [ ("set", [ Ctype.newconstr path [ element ] ], resource_type) ]
              | Resource_auth underlying, _ ->
                  begin match
                    List.find resources ~f:(fun r ->
                        String.equal r.resource_name underlying.pid_str)
                  with
                  | Some base ->
                      Ok
                        (( "auth_frag",
                           [ base.resource_type; base.resource_type ],
                           resource_type )
                        :: List.map [ "auth"; "frag"; "full" ] ~f:(fun operation ->
                            (operation, [ base.resource_type ], resource_type)))
                  | None ->
                      Error
                        (Report.error Type underlying.pid_loc
                           "Auth requires a previously declared resource module")
                  end
              | Resource_set _, None ->
                  Error (Report.error Type at "A set resource requires an element type")
            in
            let resource_operations =
              specific_operations
              @ [
                  ("id", [], resource_type);
                  ("top", [], resource_type);
                  ("valid", [ resource_type ], Predef.type_bool);
                  ("comp", [ resource_type; resource_type ], resource_type);
                  ("frame", [ resource_type; resource_type ], resource_type);
                  ("fpuAllowed", [ resource_type; resource_type ], Predef.type_bool);
                ]
            in
            let resource =
              {
                resource_name = name.pid_str;
                resource_kind;
                resource_type;
                resource_id;
                resource_operations;
                resource_descriptor;
                resource_aliases;
                resource_at = at;
              }
            in
            Ok (env, descriptors, resource :: resources, fields)
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
            let* env = value env name (core_type ~at field_type) in
            Ok
              ( env,
                descriptors,
                resources,
                {
                  field_name = name.pid_str;
                  field_owner = owner;
                  field_value = content;
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
          let library_id =
            match typed.sig_items with
            | [ { sig_desc = Tsig_module { md_id = Some id; _ }; _ } ] -> id
            | _ -> Ident.create_local library_name
          in
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
    let interface = Option.map (sibling file ".mli") ~f:load_interface in
    let* () =
      Option.value_map interface ~default:(Ok ())
        ~f:(check_interface interface_env signature)
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
    Option.iter interface ~f:(specialize_to_interface env typed);
    let proof = Option.value_map (sibling file ".proof") ~default:(Ok []) ~f:load_proof in
    Result.bind proof ~f:(fun proof ->
        Result.map (elaborate_proof_types env interface proof)
          ~f:(fun (env, proof_types, proof_resources, proof_fields, proof_aus) ->
            {
              file;
              text;
              scope;
              typed;
              comments;
              env;
              sequence;
              logical_types;
              proof_types;
              proof_resources;
              proof_fields;
              proof_aus;
              pending;
              interface;
              proof;
              libraries;
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

let logical_identifier ~functions ~loc q =
  match q with
  | S.Qdot (Qid m, op)
    when List.mem [ "Set"; "Finset"; "Map" ] m.pid_str ~equal:String.equal
         && not (List.mem functions (m.pid_str ^ "." ^ op.pid_str) ~equal:String.equal) ->
      logical_helper ~loc [ m.pid_str; op.pid_str ]
  | Qid { pid_str = "to_sequence"; _ }
    when not (List.mem functions "to_sequence" ~equal:String.equal) ->
      logical_helper ~loc [ "to_sequence" ]
  | Qid { pid_str = "==="; _ } -> logical_helper ~loc [ "equal" ]
  | Qid { pid_str = "=/="; _ } -> logical_helper ~loc [ "not_equal" ]
  | Qid { pid_str = "->" | "<->"; _ } -> logical_helper ~loc [ "implies" ]
  | Qid { pid_str = "/\\"; _ } -> Ast_helper.Exp.ident ~loc { txt = Lident "&&"; loc }
  | Qid { pid_str = "\\/"; _ } -> Ast_helper.Exp.ident ~loc { txt = Lident "||"; loc }
  | Qid { pid_str = "-"; pid_fixity = Prefix; _ } ->
      Ast_helper.Exp.ident ~loc { txt = Lident "~-"; loc }
  | _ -> Ast_helper.Exp.ident ~loc { txt = longident q; loc }

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
