(** Annotations: comments starting with [@], such as one stating the contract of a
    function: [@ r = f x requires P ensures Q]. *)

open Base

type t = { text : string; loc : Location.t }

(** The annotations among [comments]. *)
let of_comments (comments : (string * Location.t) list) : t list =
  List.filter_map comments ~f:(fun (text, loc) ->
      Option.map (String.chop_prefix text ~prefix:"@") ~f:(fun text -> { text; loc }))

(** The position in the source of the character at [offset] of [annotation]'s text, which
    starts after the comment's opening delimiter and its [@]. *)
let position (annotation : t) offset : Lexing.position =
  let start = annotation.loc.loc_start in
  let cnum = start.pos_cnum + 3 + offset in
  (* The lines the text before [offset] ends, and where the last one starts. *)
  let before = String.prefix annotation.text offset in
  let lines = String.count before ~f:(Char.equal '\n') in
  let bol =
    match String.rindex before '\n' with
    | Some i -> start.pos_cnum + 3 + i + 1
    | None -> start.pos_bol
  in
  { start with pos_cnum = cnum; pos_lnum = start.pos_lnum + lines; pos_bol = bol }

(** The tokens of [annotation]'s text, with their offsets in it. *)
let tokens (annotation : t) : (Parser.token * int * int) list =
  let lexbuf = Lexing.from_string annotation.text in
  let rec go acc =
    match Lexer.token lexbuf with
    | Parser.EOF -> List.rev acc
    | token -> go ((token, Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf) :: acc)
  in
  go []

type contract = {
  result : string option;  (** The name of the result, as [r] in [r = f x]. *)
  requires : Parsetree.expression list;
  ensures : Parsetree.expression list;
}
(** The contract of a function. *)

(** The formula of a clause: the text of [annotation] from [start] to [stop], parsed as an
    OCaml expression located in the source. *)
let formula (annotation : t) ~start ~stop : (Parsetree.expression, Report.error) Result.t
    =
  let text = String.sub annotation.text ~pos:start ~len:(stop - start) in
  let lexbuf = Lexing.from_string text in
  Lexing.set_position lexbuf (position annotation start);
  Lexing.set_filename lexbuf annotation.loc.loc_start.pos_fname;
  (* The parser reports errors by raising. *)
  try Ok (Parse.expression lexbuf)
  with exn ->
    let loc =
      {
        Location.loc_start = position annotation start;
        loc_end = position annotation stop;
        loc_ghost = false;
      }
    in
    Error
      (Option.value (Report.of_exn exn)
         ~default:(Report.error Syntax loc "This formula does not parse"))

(** The contract that [annotation] states: an optional header [r = f x1 ... xn] followed
    by clauses [requires P] and [ensures Q]. *)
let contract (annotation : t) : (contract, Report.error) Result.t =
  let error message = Error (Report.error Syntax annotation.loc message) in
  match tokens annotation with
  | exception exn -> (
      match Report.of_exn exn with
      | Some e -> Error e
      | None -> error "This annotation does not lex")
  | tokens ->
      let is_clause = function
        | Parser.LIDENT ("requires" | "ensures"), _, _ -> true
        | _ -> false
      in
      let header, clauses = List.split_while tokens ~f:(fun t -> not (is_clause t)) in
      let result =
        match header with
        | (Parser.LIDENT r, _, _) :: (Parser.EQUAL, _, _) :: _ -> Some r
        | _ -> None
      in
      (* Each clause extends to the next one, or to the end. *)
      let starts =
        List.filter_map clauses ~f:(function
          | (Parser.LIDENT keyword, start, stop) as t when is_clause t ->
              Some (keyword, start, stop)
          | _ -> None)
      in
      let ends =
        List.map
          (List.tl starts |> Option.value ~default:[])
          ~f:(fun (_, start, _) -> start)
        @ [ String.length annotation.text ]
      in
      let rec go contract = function
        | [] -> Ok contract
        | ((keyword, _, after), stop) :: rest -> (
            match formula annotation ~start:after ~stop with
            | Error e -> Error e
            | Ok f ->
                let contract =
                  if String.equal keyword "requires" then
                    { contract with requires = contract.requires @ [ f ] }
                  else { contract with ensures = contract.ensures @ [ f ] }
                in
                go contract rest)
      in
      if List.is_empty starts then
        error "Expected `requires` or `ensures` in this annotation"
      else go { result; requires = []; ensures = [] } (List.zip_exn starts ends)
