type node = Nil | Next of int * node Atomic.t
type t = { head : node Atomic.t Atomic.t; tail : node Atomic.t Atomic.t }

(* The compare_and_set leaves the head where it is, which is not a pop. *)
let rec pop_opt q =
  let old_head = Atomic.get q.head in
  match Atomic.get old_head (*@ returning Nil -> commit *) with
  | Nil -> None
  | Next (value, _) ->
      if Atomic.compare_and_set q.head old_head old_head then Some value else pop_opt q

(* The tail moves to a cell that is not linked. *)
let swing_tail q =
  let old_tail = Atomic.get q.tail in
  let fresh = Atomic.make Nil in
  if Atomic.compare_and_set q.tail old_tail fresh then () else ()
