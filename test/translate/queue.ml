(* Saturn's Michael-Scott queue, of integers: creation and pop, without backoff, and
   moving the tail on by a cell. *)

type node = Nil | Next of int * node Atomic.t
type t = { head : node Atomic.t Atomic.t; tail : node Atomic.t Atomic.t }

let create () =
  let next = Atomic.make Nil in
  let head = Atomic.make_contended next in
  let tail = Atomic.make_contended next in
  { head; tail }
(*@ initially { cells = [ next ]; values = []; head = 0; tail = 0 } *)

let rec pop_opt q =
  let old_head = Atomic.get q.head in
  match Atomic.get old_head (*@ returning Nil -> commit *) with
  | Nil -> None
  | Next (value, next) ->
      if Atomic.compare_and_set q.head old_head next then Some value else pop_opt q

let swing_tail q =
  let old_tail = Atomic.get q.tail in
  match Atomic.get old_tail with
  | Nil -> ()
  | Next (_, next) -> if Atomic.compare_and_set q.tail old_tail next then () else ()
