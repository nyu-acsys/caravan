(** Reusable finite snapshots for the supported standard-library operations. *)

type 'a t

(*@ invariant persistent (sequence : 'a t) (values [@implicit] : 'a list) *)

val empty : 'a t
(*@ result = empty
    ensures persistent result [] *)
