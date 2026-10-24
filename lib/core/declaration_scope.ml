(** Lexical boundaries within one parsed input, independent of [#line] filenames. *)

open Base

type t = { location : Location.t }

let of_lexbuf ~file lexbuf =
  { location = { (Location.in_file file) with loc_end = lexbuf.Lexing.lex_curr_p } }

let following ?scope ~(item_loc : Location.t) ~(next : Location.t option)
    (annotation : Location.t) =
  annotation.loc_start.pos_cnum >= item_loc.loc_end.pos_cnum
  && Option.for_all next ~f:(fun next ->
      annotation.loc_end.pos_cnum <= next.loc_start.pos_cnum)
  && Option.for_all scope ~f:(fun scope ->
      annotation.loc_start.pos_cnum >= scope.location.loc_start.pos_cnum
      && annotation.loc_end.pos_cnum <= scope.location.loc_end.pos_cnum)
