(** Lexical boundaries within one parsed input, independent of [#line] filenames. *)

open Base

type t = { location : Location.t }

let of_lexbuf ~file lexbuf =
  { location = { (Location.in_file file) with loc_end = lexbuf.Lexing.lex_curr_p } }

(** Whether [inner] lies within [outer], both in one input: offsets only, which [#line]
    directives leave unchanged. *)
let contains_in_input (outer : Location.t) (inner : Location.t) =
  outer.loc_start.pos_cnum <= inner.loc_start.pos_cnum
  && inner.loc_end.pos_cnum <= outer.loc_end.pos_cnum

(** Whether [a] and [b] are the same place, both in one input. *)
let same_in_input (a : Location.t) (b : Location.t) =
  a.loc_start.pos_cnum = b.loc_start.pos_cnum && a.loc_end.pos_cnum = b.loc_end.pos_cnum

(** Whether [inner], possibly from another input, lies within [outer]: the file names tell
    inputs apart. *)
let contains (outer : Location.t) (inner : Location.t) =
  String.equal outer.loc_start.pos_fname inner.loc_start.pos_fname
  && contains_in_input outer inner

(** Whether [a] and [b], possibly from different inputs, are the same place. *)
let same_place (a : Location.t) (b : Location.t) =
  String.equal a.loc_start.pos_fname b.loc_start.pos_fname && same_in_input a b

let following ?scope ~(item_loc : Location.t) ~(next : Location.t option)
    (annotation : Location.t) =
  annotation.loc_start.pos_cnum >= item_loc.loc_end.pos_cnum
  && Option.for_all next ~f:(fun next ->
      annotation.loc_end.pos_cnum <= next.loc_start.pos_cnum)
  && Option.for_all scope ~f:(fun scope -> contains_in_input scope.location annotation)
