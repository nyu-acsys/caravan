(* Saturn's queue nodes: a variant holding an atomic, and an immutable record of atomics
   holding atomics, owned through the record as own q.head c. *)

type node = Nil | Next of int * node Atomic.t
type t = { head : node Atomic.t Atomic.t; tail : node Atomic.t Atomic.t }

let create () =
  let next = Atomic.make Nil in
  { head = Atomic.make next; tail = Atomic.make next }
(*@ q = create () *)

let first (q : t) =
  let cell = Atomic.get q.head in
  match Atomic.get cell with Nil -> None | Next (v, _) -> Some v
(*@ r = first q
    requires own q.head c && own c Nil
    ensures own q.head c && own c Nil && r = None *)
