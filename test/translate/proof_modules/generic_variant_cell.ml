module type OUTPUT = sig
  type node = Nil | Next of int * node Atomic.t
  type t = node Atomic.t

  (*@ invariant is_cell (cell : t) *)
  (*@ predicate contents (cell : t) (value : node) *)

  val create : unit -> t
  (*@ cell = create () ensures is_cell cell && contents cell Nil *)

  val read : t -> node
  (*@ result = atomic read cell requires is_cell cell
      atomic requires contents cell value
      atomic ensures contents cell value && result === value *)
end

module Make () : OUTPUT = struct
  type node = Nil | Next of int * node Atomic.t
  type t = node Atomic.t

  let create () = Atomic.make Nil
  (*@ initially { value = Nil } *)

  let read (cell : t) = Atomic.get cell (*@ commit *)
end

module First = Make ()
module Second = Make ()

let independent () =
  let first = First.create () in
  let second = Second.create () in
  assert (First.read first == First.Nil);
  assert (Second.read second == Second.Nil)
