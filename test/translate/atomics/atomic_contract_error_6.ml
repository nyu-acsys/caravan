type t = int list Atomic.t

(*@ predicate stack (t : t) (xs : int list) = own t xs *)

let rec pop (t : t) =
  match Atomic.get t (*@ returning rest -> commit *) with
  | [] -> None
  | x :: rest -> if Atomic.compare_and_set t (x :: rest) rest then Some x else pop t
(*@ r = atomic pop t
    atomic requires stack t xs
    atomic ensures stack t xs *)
