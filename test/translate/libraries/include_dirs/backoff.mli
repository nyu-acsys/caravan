(** A backoff without [once], which [include_dirs.ml] calls: found only after the one next
    to it. *)

type t

val default : t
