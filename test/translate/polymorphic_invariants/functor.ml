module type PARAM = sig end

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

module Make (P : PARAM) : CELL = struct
  type 'a t = { cell : 'a Atomic.t }

  let create value = { cell = Atomic.make value }
  (*@ initially { value = value } *)

  let read (q : 'a t) = Atomic.get q.cell (*@ commit *)

  let rec set q value =
    let before = Atomic.get q.cell in
    if Atomic.compare_and_set q.cell before value (*@ performs replace *) then ()
    else set q value
end

module Arg = struct end
module OtherArg = struct end
module First = Make (Arg)
module Again = Make (Arg)
module Other = Make (OtherArg)
module Alias = First

let both () =
  let integer = First.create 17 in
  let boolean = Alias.create false in
  Again.set integer 42;
  First.set boolean true;
  (Alias.read integer, Again.read boolean)
(*@ result = both () ensures result === (42, true) *)

let other () =
  let q = Other.create true in
  Other.set q false;
  Other.read q
(*@ result = other () ensures not result *)

module Fresh () : CELL = struct
  type 'a t = { cell : 'a Atomic.t }

  let create value = { cell = Atomic.make value }
  (*@ initially { value = value } *)

  let read (q : 'a t) = Atomic.get q.cell (*@ commit *)

  let rec set q value =
    let before = Atomic.get q.cell in
    if Atomic.compare_and_set q.cell before value (*@ performs replace *) then ()
    else set q value
end

module Fresh_first = Fresh ()
module Fresh_second = Fresh ()
module Fresh_alias = Fresh_first

let fresh_both () =
  let integer = Fresh_first.create 17 in
  let boolean = Fresh_second.create false in
  Fresh_alias.set integer 42;
  Fresh_second.set boolean true;
  (Fresh_alias.read integer, Fresh_second.read boolean)
(*@ result = fresh_both () ensures result === (42, true) *)
