(** An OCaml implementation, parsed and type-checked by the compiler's own front end, with
    its interface and proof, if there are any: [f.mli] and [f.proof] next to [f.ml]. *)

open Base
module S = Caravan_spec.Spec_ast

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
          [sequence] of specifications. *)
  sequence : Path.t;  (** The type ['a sequence] of specifications. *)
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
    let interface = Option.map (sibling file ".mli") ~f:load_interface in
    Option.iter interface ~f:(specialize_to_interface env typed);
    let proof = Option.value_map (sibling file ".proof") ~default:(Ok []) ~f:load_proof in
    Result.map proof ~f:(fun proof ->
        {
          file;
          text;
          typed;
          comments;
          env;
          sequence;
          pending;
          interface;
          proof;
          libraries;
        })
  with exn -> (
    match Report.of_exn exn with
    | Some error -> Error error
    | None ->
        Error (Report.error Type (Location.in_file file) (Stdlib.Printexc.to_string exn)))

(** The OCaml type that the type [t] of an annotation at [at] denotes in [env]. The
    compiler's type checker reports errors by raising. *)
let ocaml_type (env : Env.t) ~(at : Location.t) (t : S.pty) :
    (Types.type_expr, Report.error) Result.t =
  let rec longident : S.qualid -> Longident.t = function
    | Qid id -> Lident id.pid_str
    | Qdot (q, id) ->
        Ldot ({ txt = longident q; loc = at }, { txt = id.pid_str; loc = at })
  in
  let rec core_type (t : S.pty) : Parsetree.core_type =
    match t with
    | PTtyvar id -> Ast_helper.Typ.var ~loc:at id.pid_str
    | PTtyapp (q, args) ->
        Ast_helper.Typ.constr ~loc:at
          { txt = longident q; loc = at }
          (List.map args ~f:core_type)
    | PTtuple ts ->
        Ast_helper.Typ.tuple ~loc:at (List.map ts ~f:(fun t -> (None, core_type t)))
    | PTarrow (a, b) -> Ast_helper.Typ.arrow ~loc:at Nolabel (core_type a) (core_type b)
  in
  try Ok (Typetexp.transl_simple_type env ~closed:true (core_type t)).ctyp_type
  with exn -> (
    match Report.of_exn exn with
    | Some error -> Error error
    | None -> Error (Report.error Type at (Stdlib.Printexc.to_string exn)))
