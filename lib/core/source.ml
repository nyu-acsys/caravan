(** An OCaml implementation, parsed and type-checked by the compiler's own front end, with
    its interface and proof, if there are any: [f.mli] and [f.proof] next to [f.ml]. *)

open Base
module S = Caravan_spec.Spec_ast

let ( let* ) = Result.( >>= )

type interface = {
  signature : Parsetree.signature;
  interface_comments : (string * Location.t) list;
}

type library = { library_name : string; library_id : Ident.t; library : interface }
(** A library that the file uses, which an interface [m.mli] without an implementation
    next to it declares: the module [M], trusted. *)

type t = {
  file : string;
  text : string;
  typed : Typedtree.structure;
  comments : (string * Location.t) list;  (** With their text, without delimiters. *)
  env : Env.t;
      (** The environment at the end of the file, for types in annotations, with the type
          [sequence], [finset], [set], and [map] of specifications. *)
  sequence : Path.t;  (** The type ['a sequence] of specifications. *)
  logical_types : Datatypes.t list;
      (** The collection types of specifications, identified by their declarations. *)
  proof_types : Datatypes.t list;  (** Algebraic types declared by the proof. *)
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
  { signature; interface_comments = Lexer.comments () }

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
    (proof : S.proof_decl list) : (Env.t * Datatypes.t list, Report.error) Result.t =
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
  let declarations =
    List.filter_map proof ~f:(function
      | Proof_type { type_name; type_ctors } ->
          let constructor ((name : S.id), (args : S.pty list)) =
            Ast_helper.Type.constructor ~loc:name.pid_loc
              ~args:(Pcstr_tuple (List.map args ~f:(core_type ~at:name.pid_loc)))
              { txt = name.pid_str; loc = name.pid_loc }
          in
          Some
            (Ast_helper.Type.mk ~loc:type_name.pid_loc
               ~kind:(Ptype_variant (List.map type_ctors ~f:constructor))
               { txt = type_name.pid_str; loc = type_name.pid_loc })
      | _ -> None)
  in
  let* env, reversed =
    List.fold_result declarations ~init:(env, [])
      ~f:(fun (env, descriptors) declaration ->
        let typed, _, _, _, env =
          Typemod.type_structure env [ Ast_helper.Str.type_ Recursive [ declaration ] ]
        in
        let typed_declarations =
          List.concat_map typed.str_items ~f:(fun item ->
              match item.str_desc with Tstr_type (_, ds) -> ds | _ -> [])
        in
        let* added =
          Result.all (List.map typed_declarations ~f:Datatypes.of_declaration)
        in
        Ok (env, List.rev_append added descriptors))
  in
  Ok (env, List.rev reversed)

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
    let comments = Lexer.comments () in
    Env.set_current_unit
      (Unit_info.make ~check_modname:false ~source_file:file Impl
         (Stdlib.Filename.remove_extension file));
    let typed, _, _, _, env = Typemod.type_structure env parsed in
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
    let logical_types = List.rev logical_types in
    let interface = Option.map (sibling file ".mli") ~f:load_interface in
    Option.iter interface ~f:(specialize_to_interface env typed);
    let proof = Option.value_map (sibling file ".proof") ~default:(Ok []) ~f:load_proof in
    Result.bind proof ~f:(fun proof ->
        Result.map (elaborate_proof_types env interface proof)
          ~f:(fun (env, proof_types) ->
            {
              file;
              text;
              typed;
              comments;
              env;
              sequence;
              logical_types;
              proof_types;
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
