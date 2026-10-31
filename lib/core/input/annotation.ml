(** Annotations: comments starting with [@], such as one stating the contract of a
    function: [@ r = f x requires P ensures Q]. *)

open Base
open Caravan_spec

type t = {
  text : string;
  loc : Location.t;
  origin : Lexing.position option;
      (** Where [text] is written, if not in the comment at [loc]: in a proof outline. *)
}

(** The annotations among [comments]. *)
let of_comments (comments : (string * Location.t) list) : t list =
  List.filter_map comments ~f:(fun (text, loc) ->
      Option.map (String.chop_prefix text ~prefix:"@") ~f:(fun text ->
          { text; loc; origin = None }))

(** A lexer buffer reading [annotation]'s text at its place in the source, after the
    comment's opening delimiter and its [@]. *)
let lexbuf (annotation : t) =
  let lexbuf = Lexing.from_string annotation.text in
  let start =
    match annotation.origin with
    | Some origin -> origin
    | None ->
        let start = annotation.loc.loc_start in
        { start with pos_cnum = start.pos_cnum + 3 }
  in
  Lexing.set_position lexbuf start;
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
  | Ghost_module
  | Ghost
  | Scope
  | Returns
  | Proof
  | Manual
  | Linearization
  | Initially
  | Initializes
  | Trusted

(** What [annotation] states, by its first word. *)
let kind (annotation : t) =
  match
    String.split_on_chars
      (String.strip annotation.text)
      ~on:[ ' '; '\n'; '\t'; '\r'; '(' ]
  with
  | ("invariant" | "variant") :: _ -> Loop
  | "predicate" :: _ -> Predicate
  | "module" :: _ -> Ghost_module
  | ("fold" | "unfold" | "assert" | "lemma") :: _ -> Ghost
  | ("Ghost.scope" | "Ghost.State.scope") :: _ -> Scope
  | "Ghost.returns" :: _ -> Returns
  | "proof" :: _ -> Proof
  | [ "manual" ] -> Manual
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
  | Spec_ast.Syntax_error (loc, message) -> Error (Report.error Syntax loc message)

(** Interface invariants declare resources; implementation invariants annotate loops. *)
let invariant_declaration (annotation : t) =
  Poly.equal (kind annotation) Loop
  && String.is_prefix (String.strip annotation.text) ~prefix:"invariant"

let predicate_declaration ~interface annotation =
  Poly.equal (kind annotation) Predicate || (interface && invariant_declaration annotation)

let predicate (annotation : t) =
  parse annotation
    (if invariant_declaration annotation then Spec_parser.invariant_declaration
     else Spec_parser.predicate)

let ghost_module (annotation : t) = parse annotation Spec_parser.ghost_module_declaration
let ghost_stmts (annotation : t) = parse annotation Spec_parser.ghost_stmts
let linearization (annotation : t) = parse annotation Spec_parser.linearization
let initially (annotation : t) = parse annotation Spec_parser.initially
let scope (annotation : t) = parse annotation Spec_parser.scope
let returns (annotation : t) = parse annotation Spec_parser.return_adapter

let without_keyword (annotation : t) keyword =
  let stripped = String.lstrip annotation.text in
  match String.chop_prefix stripped ~prefix:keyword with
  | None -> annotation
  | Some body ->
      let leading = String.length annotation.text - String.length stripped in
      let text =
        String.prefix annotation.text leading
        ^ String.make (String.length keyword) ' '
        ^ body
      in
      { annotation with text }

let initializes (annotation : t) =
  parse (without_keyword annotation "initializes") Spec_parser.term_eof

let proof (annotation : t) =
  parse (without_keyword annotation "proof") Spec_parser.proof_expr_eof

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
