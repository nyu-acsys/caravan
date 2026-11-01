(**************************************************************************)
(*                                                                        *)
(*  GOSPEL -- A Specification Language for OCaml                          *)
(*                                                                        *)
(*  Copyright (c) 2018- The VOCaL Project                                 *)
(*                                                                        *)
(*  This software is free software, distributed under the MIT license     *)
(*  (as described in file LICENSE enclosed).                              *)
(**************************************************************************)

{
  (* Gospel's lexer (ulexer.mll of github.com/ocaml-gospel/gospel at ce26d16), for
     Caravan's contracts: with the keywords of terms and contracts, and match. *)

  open Lexing
  open Spec_parser

  exception Error = Spec_ast.Syntax_error

  let error lexbuf message =
    let loc =
      { Location.loc_start = lexbuf.lex_start_p; loc_end = lexbuf.lex_curr_p;
        loc_ghost = false }
    in
    raise (Error (loc, message))

  let keywords = Hashtbl.create 97

  let () =
    List.iter
      (fun (x, y) -> Hashtbl.add keywords x y)
      [
        "else", ELSE;
        "ensures", ENSURES;
        "exists", EXISTS;
        "false", FALSE;
        "forall", FORALL;
        "if", IF;
        "action", ACTION;
        "consumes", CONSUMES;
        "continues", CONTINUES;
        "end", END;
        "helps", HELPS;
        "on", ON;
        "wait", WAIT;
        "linearizes", LINEARIZES;
        "assert", ASSERT;
        "at", AT;
        "atomic", ATOMIC;
        "begin", BEGIN;
        "commit", COMMIT;
        "fold", FOLD;
        "fun", FUN;
        "in", IN;
        "initially", INITIALLY;
        "invariant", INVARIANT;
        "let", LET;
        "lemma", LEMMA;
        "match", MATCH;
        "mod", OP3 "mod";
        "module", MODULE;
        "not", NOT;
        "of", OF;
        "old", OLD;
        "performs", PERFORMS;
        "predicate", PREDICATE;
        "proof", PROOF;
        "pure", PURE;
        "requires", REQUIRES;
        "returning", RETURNING;
        "returns", RETURNS;
        "struct", STRUCT;
        "then", THEN;
        "type", TYPE;
        "true", TRUE;
        "unfold", UNFOLD;
        "variant", VARIANT;
        "view", VIEW;
        "with", WITH;
      ]

  (* to translate escape sequences *)

  let digit_value c =
    match c with
    | 'a' .. 'f' -> 10 + Char.code c - Char.code 'a'
    | 'A' .. 'F' -> 10 + Char.code c - Char.code 'A'
    | '0' .. '9' -> Char.code c - Char.code '0'
    | _ -> assert false

  let num_value lexbuf ~base ~first ~last =
    let c = ref 0 in
    for i = first to last do
      let v = digit_value (Lexing.lexeme_char lexbuf i) in
      assert(v < base);
      c := (base * !c) + v
    done;
    !c

  let char_for_backslash = function
    | 'n' -> '\010'
    | 'r' -> '\013'
    | 'b' -> '\008'
    | 't' -> '\009'
    | c   -> c

  let illegal_escape lexbuf reason =
    error lexbuf (Printf.sprintf "Illegal backslash escape in string or character (%s): %s"
      (Lexing.lexeme lexbuf) reason)

  let char_for_decimal_code lexbuf i =
    let c = num_value lexbuf ~base:10 ~first:i ~last:(i+2) in
    if (c < 0 || c > 255) then
      illegal_escape lexbuf
        (Printf.sprintf
           "%d is outside the range of legal characters (0-255)." c)
    else Char.chr c

  let char_for_octal_code lexbuf i =
    let c = num_value lexbuf ~base:8 ~first:i ~last:(i+2) in
    if (c < 0 || c > 255) then
      illegal_escape lexbuf
        (Printf.sprintf
           "o%o (=%d) is outside the range of legal characters (0-255)." c c)
    else Char.chr c

  let char_for_hexadecimal_code lexbuf i =
    Char.chr (num_value lexbuf ~base:16 ~first:i ~last:(i+1))

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  (* The lines that the lexeme spans, as [atomic] and [requires] on two. *)
  let newlines lexbuf =
    let start = Lexing.lexeme_start lexbuf in
    String.iteri
      (fun i c ->
        if c = '\n' then
          let pos = lexbuf.lex_curr_p in
          lexbuf.lex_curr_p <-
            { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = start + i + 1 })
      (Lexing.lexeme lexbuf)
}


let newline = '\n'
let space = [' ' '\t' '\r']
let lalpha = ['a'-'z' '_']
let ualpha = ['A'-'Z']
let alpha = lalpha | ualpha
let digit = ['0'-'9']
let lident = lalpha (alpha | digit | '\'')*
let uident = ualpha (alpha | digit | '\'')*
let hexadigit = ['0'-'9' 'a'-'f' 'A'-'F']

let decimal_literal =
  ['0'-'9'] ['0'-'9' '_']*
let hex_digit =
  ['0'-'9' 'A'-'F' 'a'-'f']
let hex_literal =
  '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']['0'-'9' 'A'-'F' 'a'-'f' '_']*
let oct_literal =
  '0' ['o' 'O'] ['0'-'7'] ['0'-'7' '_']*
let bin_literal =
  '0' ['b' 'B'] ['0'-'1'] ['0'-'1' '_']*
let int_literal =
  decimal_literal | hex_literal | oct_literal | bin_literal
let float_literal =
  ['0'-'9'] ['0'-'9' '_']*
  ('.' ['0'-'9' '_']* )?
  (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']* )?
let hex_float_literal =
  '0' ['x' 'X']
  ['0'-'9' 'A'-'F' 'a'-'f'] ['0'-'9' 'A'-'F' 'a'-'f' '_']*
  ('.' ['0'-'9' 'A'-'F' 'a'-'f' '_']* )?
  (['p' 'P'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']* )?
let int_literal_modifier = 'i'

let op_char_1 = ['=' '<' '>' '~']
let op_char_2 = ['+' '-']
let op_char_3 = ['*' '/' '\\' '%']
let op_char_4 = ['!' '$' '&' '?' '@' '^' '.' ':' '|' '#']
let op_char_1234 = op_char_1 | op_char_2 | op_char_3 | op_char_4
let op_char_234  = op_char_2 | op_char_3 | op_char_4
let op_char_34   = op_char_3 | op_char_4

let op_char_pref = ['!' '?']

rule token = parse
  | "~fraction"
      { FRACTION }
  | "Set.of_predicate"
      { SET_OF_PREDICATE }
  | "[@" space* ([^ ' ' '\n' ']']+ (' '+ [^ ' ' '\n' ']']+)* as lbl) space* ']'
      { ATTRIBUTE lbl }
  | newline
      { newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | "atomic" (space | newline)+ "requires"
      { newlines lexbuf; ATOMIC_REQUIRES }
  | "atomic" (space | newline)+ "ensures"
      { newlines lexbuf; ATOMIC_ENSURES }
  | int_literal as lit
      { INTEGER (lit, None) }
  | (int_literal as lit) (int_literal_modifier as modif)
      { INTEGER (lit, Some modif) }
  | (float_literal | hex_float_literal) as s
      { FLOAT s }
  | "\'" ([^ '\\' '\'' '\010' '\013'] as c) "\'"
    { CHAR c }
  | "\'\\" (['\\' '\'' '\"' 'n' 't' 'b' 'r' ' '] as c) "\'"
    { CHAR (char_for_backslash c) }
  | "\'\\" ['0'-'9'] ['0'-'9'] ['0'-'9'] "\'"
    { CHAR(char_for_decimal_code lexbuf 2) }
  | "\'\\" 'o' ['0'-'7'] ['0'-'7'] ['0'-'7'] "\'"
    { CHAR(char_for_octal_code lexbuf 3) }
  | "\'\\" 'x' ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F'] "\'"
    { CHAR(char_for_hexadecimal_code lexbuf 3) }
  | "(*"
      { comment lexbuf; token lexbuf }
  | ","
      { COMMA }
  | ";"
      { SEMICOLON }
  | "{"
      { LEFTBRC }
  | "}"
      { RIGHTBRC }
  | "."
      { DOT }
  | ":"
      { COLON }
  | "::"
      { COLONCOLON }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "->"
      { ARROW }
  | "~>"
      { LEADSTO }
  | "<->"
      { LRARROW }
  | "&&"
      { AMPAMP }
  | "||"
      { BARBAR }
  | "/\\"
      { CONJ }
  | "\\/"
      { DISJ }
  | ".."
      { DOTDOT }
  | "|"
      { BAR }
  | "="
      { EQUAL }
  | "<>"
      { LTGT }
  | "'" (lident as id)
      { QUOTE_LIDENT id }
  | "`" (lident as id) "`"
      { BACKQUOTE_LIDENT id }
  | '_'
      { UNDERSCORE }
  | lident as id
      { try Hashtbl.find keywords id with Not_found -> LIDENT id }
  | uident as id
            { UIDENT id }
  | "[]"
      { LEFTSQRIGHTSQ }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | "*" { STAR }
  | op_char_pref op_char_4* as s
      { OPPREF s }
  | op_char_1234* op_char_1 op_char_1234* as s
      { OP1 s }
  | op_char_234*  op_char_2 op_char_234*  as s
      { OP2 s }
  | op_char_34*   op_char_3 op_char_34*  as s
      { OP3 s }
  | op_char_4+ as s
      { OP4 s }
  | "\""
      { STRING (string (Buffer.create 128) lexbuf) }
  | eof
      { EOF }
  | _ as c
      { error lexbuf (Printf.sprintf "Illegal character %C" c) }

and comment = parse
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | newline
      { newline lexbuf; comment lexbuf }
  | eof
      { error lexbuf "This comment is not terminated" }
  | _
      { comment lexbuf }

and string buf = parse
  | "\""
      { Buffer.contents buf }
  | "\\" newline
      { new_line lexbuf;
        string_skip_spaces buf lexbuf }
  | "\\" (_ as c)
      { Buffer.add_char buf (char_for_backslash c);
        string buf lexbuf }
  | newline
      { new_line lexbuf;
        Buffer.add_char buf '\n';
        string buf lexbuf }
  | eof
      { error lexbuf "This string is not terminated" }
  | _ as c
      { Buffer.add_char buf c;
        string buf lexbuf }

and string_skip_spaces buf = parse
  | [' ' '\t']*
      { string buf lexbuf }
