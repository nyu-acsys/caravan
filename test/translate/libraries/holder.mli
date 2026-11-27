(** A library whose interface opens another library module. *)

open Cell

val read : t -> int
(*@ r = read c
    requires holds c v
    ensures holds c v && r = v *)
