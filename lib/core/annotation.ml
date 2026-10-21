(** Annotations: comments starting with [@], such as one stating the contract of a
    function: [@ r = f x requires P ensures Q]. *)

open Base
open Caravan_spec

type t = { text : string; loc : Location.t }

(** The annotations among [comments]. *)
let of_comments (comments : (string * Location.t) list) : t list =
  List.filter_map comments ~f:(fun (text, loc) ->
      Option.map (String.chop_prefix text ~prefix:"@") ~f:(fun text -> { text; loc }))

(** A lexer buffer reading [annotation]'s text at its place in the source, after the
    comment's opening delimiter and its [@]. *)
let lexbuf (annotation : t) =
  let lexbuf = Lexing.from_string annotation.text in
  let start = annotation.loc.loc_start in
  Lexing.set_position lexbuf { start with pos_cnum = start.pos_cnum + 3 };
  Lexing.set_filename lexbuf start.pos_fname;
  lexbuf

let lexeme_loc lexbuf =
  {
    Location.loc_start = Lexing.lexeme_start_p lexbuf;
    loc_end = Lexing.lexeme_end_p lexbuf;
    loc_ghost = false;
  }

(** The contract that [annotation] states: an optional header [r = f x1 ... xn] followed
    by its clauses. The lexer and the parser report errors by raising. *)
let contract (annotation : t) : (Spec_ast.contract, Report.error) Result.t =
  let lexbuf = lexbuf annotation in
  try Ok (Spec_parser.contract Spec_lexer.token lexbuf) with
  | Spec_lexer.Error (loc, message) -> Error (Report.error Syntax loc message)
  | Spec_parser.Error -> Error (Report.error Syntax (lexeme_loc lexbuf) "Syntax error")
