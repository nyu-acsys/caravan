module type CELL = sig
  type 'a t

  (*@ invariant is_cell (q : 'a t) *)
  (*@ predicate cell (q : 'a t) (value : 'a) *)

  val create : 'a -> 'a t
  (*@ q = create value ensures is_cell q && cell q value *)

  val read : 'a t -> 'a
  (*@ result = atomic read q
      requires is_cell q
      atomic requires cell q value
      atomic ensures cell q value && result === value *)

  val set : 'a t -> 'a -> unit
  (*@ atomic set q value
      requires is_cell q
      atomic requires cell q before
      atomic ensures cell q value *)
end

module Cell : CELL = struct
  type 'a t = 'a Atomic.t

  let create value = Atomic.make value
  (*@ initially { value = value } *)

  let read (q : 'a t) = Atomic.get q (*@ commit *)

  let rec set q value =
    let before = Atomic.get q in
    if Atomic.compare_and_set q before value (*@ performs replace *) then ()
    else set q value
end

module Alias = Cell

let direct (q : 'a Cell.t) = Cell.read q
(*@ result = direct q
    requires Cell.is_cell q && Cell.cell q before
    ensures Cell.is_cell q && Cell.cell q before && result === before *)

let integer () =
  let q = Cell.create 17 in
  Alias.set q 42;
  Cell.read q
(*@ result = integer () ensures result === 42 *)

let boolean () =
  let q = Alias.create false in
  Cell.set q true;
  Alias.read q
(*@ result = boolean () ensures result *)
