type t = int list Atomic.t

(*@ predicate stack (t : t) (xs : int list) = own t xs *)

(* An empty stack linearizes at the read, which says nothing. *)
let rec pop_opt (t : t) =
  match Atomic.get t with
  | [] -> None
  | hd :: tail as before ->
      if Atomic.compare_and_set t before tail then Some hd else pop_opt t
(*@ r = atomic pop_opt t
    atomic requires stack t xs
    atomic ensures match xs with
      | [] -> r = None && stack t []
      | x :: xs' -> r = Some x && stack t xs' *)
