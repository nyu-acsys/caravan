module type OUTPUT = sig
  type t = int Atomic.t
  (*@ invariant is_counter (c : t) *)
  (*@ predicate counter (c : t) (n : int) *)

  val create : unit -> t
  (*@ c = create () ensures is_counter c && counter c 0 *)

  val set_one : t -> unit
  (*@ atomic set_one c requires is_counter c
      atomic requires counter c n
      atomic ensures counter c 1 && n = 0 *)

  val read : t -> int
  (*@ result = atomic read c requires is_counter c
      atomic requires counter c n
      atomic ensures counter c n && result = n *)
end

module World = struct
  module Make () : OUTPUT = struct
    type t = int Atomic.t

    let create () = Atomic.make 0
    (*@ initially { value = 0 } *)

    let rec set_one c =
      if Atomic.compare_and_set c 0 1 (*@ performs set_one *) then () else set_one c

    let read (c : t) = Atomic.get c (*@ commit *)
  end

  module One = Make ()
  module Two = Make ()
  module Alias = One
end

let read_both () =
  let first = World.One.create () in
  let second = World.Two.create () in
  World.One.set_one first;
  World.Two.set_one second;
  World.Alias.read first + World.Two.read second
(*@ result = read_both () ensures result = 2 *)
