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

type kind =
  | Contract
  | Loop
  | Predicate
  | Ghost
  | Linearization
  | Initially
  | Initializes
  | Trusted

(** What [annotation] states, by its first word. *)
let kind (annotation : t) =
  match String.split_on_chars (String.strip annotation.text) ~on:[ ' '; '\n'; '\t' ] with
  | ("invariant" | "variant") :: _ -> Loop
  | "predicate" :: _ -> Predicate
  | ("fold" | "unfold" | "assert" | "lemma") :: _ -> Ghost
  | ("commit" | "returning" | "performs") :: _ -> Linearization
  | "initially" :: _ -> Initially
  | "initializes" :: _ -> Initializes
  | [ "trusted" ] -> Trusted
  | _ -> Contract

(** Parses [annotation] with [entry]; the lexer and the parser report errors by raising.
*)
let parse (annotation : t) entry =
  let lexbuf = lexbuf annotation in
  try Ok (entry Spec_lexer.token lexbuf) with
  | Spec_lexer.Error (loc, message) -> Error (Report.error Syntax loc message)
  | Spec_parser.Error -> Error (Report.error Syntax (lexeme_loc lexbuf) "Syntax error")

let predicate (annotation : t) = parse annotation Spec_parser.predicate
let ghost_stmts (annotation : t) = parse annotation Spec_parser.ghost_stmts
let linearization (annotation : t) = parse annotation Spec_parser.linearization
let initially (annotation : t) = parse annotation Spec_parser.initially

let initializes (annotation : t) =
  let keyword = "initializes" in
  let stripped = String.lstrip annotation.text in
  match String.chop_prefix stripped ~prefix:keyword with
  | None -> parse annotation Spec_parser.term_eof
  | Some body ->
      let leading = String.length annotation.text - String.length stripped in
      let text =
        String.prefix annotation.text leading
        ^ String.make (String.length keyword) ' '
        ^ body
      in
      parse { annotation with text } Spec_parser.term_eof

(** The specification of a loop that [annotation] states: its invariants and variants. *)
let loop_spec (annotation : t) : (Spec_ast.loop_spec, Report.error) Result.t =
  let lexbuf = lexbuf annotation in
  try Ok (Spec_parser.loop_spec Spec_lexer.token lexbuf) with
  | Spec_lexer.Error (loc, message) -> Error (Report.error Syntax loc message)
  | Spec_parser.Error -> Error (Report.error Syntax (lexeme_loc lexbuf) "Syntax error")

(** The contract that [annotation] states: an optional header [r = f x1 ... xn] followed
    by its clauses. The lexer and the parser report errors by raising. *)
let contract (annotation : t) : (Spec_ast.contract, Report.error) Result.t =
  let lexbuf = lexbuf annotation in
  try Ok (Spec_parser.contract Spec_lexer.token lexbuf) with
  | Spec_lexer.Error (loc, message) -> Error (Report.error Syntax loc message)
  | Spec_parser.Error -> Error (Report.error Syntax (lexeme_loc lexbuf) "Syntax error")
