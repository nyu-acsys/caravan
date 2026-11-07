type t = int list Atomic.t

(*@ predicate stack (t : t) (xs : int list) = own t xs *)

(* The annotation follows the match, not the read. *)
let top (t : t) = match Atomic.get t with [] -> None | x :: _ -> Some x
(*@ commit *)
(*@ r = atomic top t
    atomic requires stack t xs
    atomic ensures stack t xs *)
