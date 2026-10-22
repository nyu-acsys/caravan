(** Saturn's exponential backoff, trusted: it touches no shared state. *)

type t

val default : t
val once : t -> t
