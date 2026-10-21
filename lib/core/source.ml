(** An OCaml implementation, parsed and type-checked by the compiler's own front end. *)

open Base

type t = {
  file : string;
  typed : Typedtree.structure;
  comments : (string * Location.t) list;  (** With their text, without delimiters. *)
  env : Env.t;  (** The environment at the end of the file, for types in annotations. *)
}

(** Parses and type-checks [file], in the environment of the standard library. The front
    end reports errors by raising; they are returned here. *)
let load (file : string) : (t, Report.error) Result.t =
  try
    Compmisc.init_path ();
    (* Caravan reports what OCaml warns about that matters to it, as a non-exhaustive match. *)
    let (_ : Warnings.alert option) = Warnings.parse_options false "-a" in
    let env = Compmisc.initial_env () in
    let lexbuf = Lexing.from_string (Stdio.In_channel.read_all file) in
    Location.init lexbuf file;
    Location.input_name := file;
    Lexer.init ();
    let parsed = Parse.implementation lexbuf in
    let comments = Lexer.comments () in
    Env.set_current_unit
      (Unit_info.make ~check_modname:false ~source_file:file Impl
         (Stdlib.Filename.remove_extension file));
    let typed, _, _, _, env = Typemod.type_structure env parsed in
    Ok { file; typed; comments; env }
  with exn -> (
    match Report.of_exn exn with
    | Some error -> Error error
    | None ->
        Error (Report.error Type (Location.in_file file) (Stdlib.Printexc.to_string exn)))

module S = Caravan_spec.Spec_ast

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
