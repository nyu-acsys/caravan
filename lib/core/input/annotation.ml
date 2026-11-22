(** Annotations: comments starting with [@], such as one stating the contract of a
    function: [@ r = f x requires P ensures Q]. *)

open Base
open Caravan_spec

type outline = {
  target : Location.t option;
      (** The source expression explicitly selected by an outline scope. *)
  export : (string * Spec_ast.pat) option;
      (** The key under which the step keeps the value it exports, and its pattern. *)
  imports : (string * Spec_ast.pat) list;
      (** The exports of earlier steps that the step uses, by key and pattern. *)
  lets : (Spec_ast.pat * Spec_ast.proof_expr) list;
      (** The outline's pure bindings that the step uses, in order. *)
  body_imports : (string * Spec_ast.pat) list;
      (** The exports of steps in a loop's body that the witnesses of its invariant use,
          at the end of each iteration. *)
}
(** What a step of a proof outline shares with the other steps. *)

type origin = {
  position : Lexing.position;
      (** The lexer position, accounting for synthetic prefixes. *)
  loc : Location.t;  (** The original text's range in the proof outline. *)
}

type t = {
  text : string;
  loc : Location.t;
  origin : origin option;
      (** Where [text] is written, if not in the comment at [loc]: in a proof outline. *)
  outline : outline option;
}

(** The annotations among [comments]. *)
let of_comments (comments : (string * Location.t) list) : t list =
  List.filter_map comments ~f:(fun (text, loc) ->
      Option.map (String.chop_prefix text ~prefix:"@") ~f:(fun text ->
          { text; loc; origin = None; outline = None }))

(** A lexer buffer reading [annotation]'s text at its place in the source, after the
    comment's opening delimiter and its [@]. *)
let lexbuf (annotation : t) =
  let lexbuf = Lexing.from_string annotation.text in
  let start =
    match annotation.origin with
    | Some origin -> origin.position
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
  | ("fold" | "unfold" | "assert" | "cut" | "lemma") :: _ -> Ghost
  | ( "Ghost.scope" | "Ghost.State.scope" | "Ghost.frozen_scope"
    | "Ghost.State.frozen_scope" | "Ghost.published_scope" | "Ghost.State.published_scope"
    | "Ghost.release_scope" | "Ghost.acquire_scope" | "Ghost.State.release_scope"
    | "Ghost.State.acquire_scope" )
    :: _ ->
      Scope
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
  try
    let contract = Spec_parser.contract Spec_lexer.token lexbuf in
    Result.map (Callable_contract.validate (Some contract)) ~f:(fun () -> contract)
  with
  | Spec_lexer.Error (loc, message) -> Error (Report.error Syntax loc message)
  | Spec_parser.Error -> Error (Report.error Syntax (lexeme_loc lexbuf) "Syntax error")
  | Spec_ast.Syntax_error (loc, message) -> Error (Report.error Syntax loc message)

(** The unique contract following a declaration in its lexical scope. *)
let contract_after ?scope ~item_loc ~next annotations =
  let follows (annotation : t) =
    Declaration_scope.following ?scope ~item_loc ~next annotation.loc
    && Poly.equal (kind annotation) Contract
  in
  match List.filter annotations ~f:follows with
  | [] -> Ok None
  | [ annotation ] ->
      Result.map (contract annotation) ~f:(fun contract -> Some (contract, annotation))
  | _ :: annotation :: _ ->
      Error (Report.error Type annotation.loc "A function has at most one contract")
