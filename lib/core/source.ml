(** An OCaml implementation, parsed and type-checked by the compiler's own front end. *)

open Base

type t = {
  file : string;
  typed : Typedtree.structure;
  comments : (string * Location.t) list;  (** With their text, without delimiters. *)
}

(** Parses and type-checks [file], in the environment of the standard library. The front
    end reports errors by raising; they are returned here. *)
let load (file : string) : (t, Report.error) Result.t =
  try
    Compmisc.init_path ();
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
    let typed, _, _, _, _ = Typemod.type_structure env parsed in
    Ok { file; typed; comments }
  with exn -> (
    match Report.of_exn exn with
    | Some error -> Error error
    | None ->
        Error (Report.error Type (Location.in_file file) (Stdlib.Printexc.to_string exn)))
