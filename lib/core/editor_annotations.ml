(** Contracts attached by the front end, with their original source text. *)

open Base
open Caravan_spec

type clause = { keyword : string; text : string; loc : Location.t }

type t = {
  loc : Location.t;
  source : string;
  source_loc : Location.t;
  clauses : clause list;
}

let keyword = function
  | Spec_parser.REQUIRES -> Some "requires"
  | ENSURES -> Some "ensures"
  | ATOMIC_REQUIRES -> Some "atomic requires"
  | ATOMIC_ENSURES -> Some "atomic ensures"
  | RAISES -> Some "raises"
  | ATOMIC_RAISES -> Some "atomic raises"
  | VARIANT -> Some "variant"
  | PURE -> Some "pure"
  | CONTINUES -> Some "continues"
  | ATOMIC -> Some "atomic"
  | _ -> None

let source_start annotation = (Annotation.lexbuf annotation).lex_curr_p

let advance (start : Lexing.position) text =
  String.fold text ~init:start ~f:(fun position character ->
      let pos_cnum = position.pos_cnum + 1 in
      if Char.equal character '\n' then
        { position with pos_cnum; pos_lnum = position.pos_lnum + 1; pos_bol = pos_cnum }
      else { position with pos_cnum })

let source_location (annotation : Annotation.t) =
  match annotation.origin with
  | None -> annotation.loc
  | Some loc_start ->
      {
        Location.loc_start;
        loc_end = advance loc_start annotation.text;
        loc_ghost = false;
      }

let clauses (annotation : Annotation.t) =
  let base = (source_start annotation).pos_cnum in
  let slice start finish =
    String.sub annotation.text ~pos:(start - base) ~len:(finish - start) |> String.strip
  in
  let scan token lexbuf =
    let finish current stop found =
      match current with
      | None -> found
      | Some (keyword, (start : Lexing.position), text_start) ->
          {
            keyword;
            text = slice text_start stop.Lexing.pos_cnum;
            loc = { Location.loc_start = start; loc_end = stop; loc_ghost = false };
          }
          :: found
    in
    let rec loop current stop found =
      let next = token lexbuf in
      let at = Annotation.lexeme_loc lexbuf in
      match next with
      | Spec_parser.EOF -> List.rev (finish current stop found)
      | _ ->
          begin match keyword next with
          | Some keyword ->
              let found = finish current stop found in
              loop (Some (keyword, at.loc_start, at.loc_end.pos_cnum)) at.loc_end found
          | None -> loop current at.loc_end found
          end
    in
    loop None lexbuf.Lexing.lex_curr_p []
  in
  Annotation.parse annotation scan

let collect (scopes : Program_scopes.t) =
  List.filter_map scopes.funcs ~f:(fun (func : Procedures.func) ->
      Option.bind func.contract_origin ~f:(fun annotation ->
          let source_loc = source_location annotation in
          let file = source_loc.loc_start.pos_fname in
          if
            String.equal func.loc.loc_start.pos_fname scopes.source.file
            && List.exists [ ".mli"; ".proof" ] ~f:(fun suffix ->
                String.is_suffix file ~suffix)
          then
            match clauses annotation with
            | Error _ -> None
            | Ok clauses ->
                Some
                  {
                    loc = func.name_loc;
                    source =
                      String.concat ~sep:"." (func.namespace @ [ Ident.name func.id ]);
                    source_loc;
                    clauses;
                  }
          else None))
  |> List.dedup_and_sort ~compare:(fun left right ->
      Poly.compare (left.loc, left.source_loc) (right.loc, right.source_loc))
