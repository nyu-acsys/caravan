(* Saturn's Michael-Scott queue, of integers: creation, push and pop, without backoff, and
   moving the tail on by a cell. fix_tail takes the queue rather than its tail, whose
   invariant it needs. *)

type node = Nil | Next of int * node Atomic.t
type t = { head : node Atomic.t Atomic.t; tail : node Atomic.t Atomic.t }

let create () =
  let next = Atomic.make Nil in
  let head = Atomic.make_contended next in
  let tail = Atomic.make_contended next in
  { head; tail }
(*@ initially { cells = [ next ]; values = []; head = 0; tail = 0 } *)

let rec fix_tail q new_tail =
  let old_tail = Atomic.get q.tail in
  if Atomic.get new_tail == Nil && not (Atomic.compare_and_set q.tail old_tail new_tail)
  then fix_tail q new_tail
(*@ fix_tail q new_tail
    requires is_queue q
    requires past (mem new_tail s.cells) *)

let push q value =
  let rec find_tail_and_enq curr_end node =
    if not (Atomic.compare_and_set curr_end Nil node) then
      match Atomic.get curr_end with
      | Nil -> find_tail_and_enq curr_end node
      | Next (_, n) -> find_tail_and_enq n node
    (*@ find_tail_and_enq curr_end node
      continues push
      requires past (mem curr_end s.cells)
      requires node = Next (v, c) && own c Nil
      ensures past (mem c s.cells) *)
  in
  let new_tail = Atomic.make Nil in
  let newnode = Next (value, new_tail) in
  let old_tail = Atomic.get q.tail in
  if not (Atomic.compare_and_set old_tail Nil newnode) then
    begin match Atomic.get old_tail with
    | Nil -> find_tail_and_enq old_tail newnode
    | Next (_, n) -> find_tail_and_enq n newnode
    end;
  if not (Atomic.compare_and_set q.tail old_tail new_tail) then fix_tail q new_tail

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

(* If the head's cell is the last at the first read, the call waits for it to be linked,
   which commits the call with false; it commits with true if the cell is still the last
   at the second read. *)
let is_empty q =
  Atomic.get
    (Atomic.get
       q.head
       (*@ returning c ->
          if c <> s.cells.(length s.values) then commit false
          else wait in s.waiting on c *))
  (*@ returning Nil -> commit true *)
  == Nil
