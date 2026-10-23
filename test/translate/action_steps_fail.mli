type t

(*@ invariant is_counter (c : t) *)
(*@ predicate counter (c : t) (n : int) *)

val create : unit -> t
(*@ c = create ()
    ensures is_counter c && counter c 0 *)

val set_one : t -> unit
(*@ atomic set_one c
    requires is_counter c
    atomic requires counter c n
    atomic ensures counter c 1 && n = 0 *)

val wrong_action : t -> unit
(*@ atomic wrong_action c
    requires is_counter c
    atomic requires counter c n
    atomic ensures counter c 1 && n = 0 *)

val forbidden_update : t -> unit
(*@ forbidden_update c requires is_counter c *)

val wrong_result : t -> int
(*@ r = atomic wrong_result c
    requires is_counter c
    atomic requires counter c n
    atomic ensures counter c n && r = 2 *)
