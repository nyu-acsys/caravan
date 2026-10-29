module type INPUT = sig end

module type OUTPUT = sig
  type t = int Atomic.t
  (*@ invariant live (root : t) *)

  val create : unit -> t
  (*@ root = create () ensures live root *)

  val remember : t -> t -> unit
  (*@ remember root x requires live root
      ensures live root
      ensures past (mem x s.cells) *)
end

module A = struct end
module B = struct end

module Make (X : INPUT) : OUTPUT = struct
  type t = int Atomic.t

  let create () = Atomic.make 0
  (*@ initially { cells = [] } *)

  let remember (root : t) (x : t) = ()
end

module One = Make (A)
module Two = Make (B)

let forward (root : One.t) (x : One.t) = One.remember root x
(*@ forward root x requires One.live root
    requires past (mem x s.cells)
    ensures One.live root
    ensures past (mem x s.cells) *)

let forward_two (root : Two.t) (x : Two.t) = Two.remember root x
(*@ forward_two root x requires Two.live root
    requires past (mem x s.cells)
    ensures Two.live root
    ensures past (mem x s.cells) *)

module Again = Make (A)
module Alias = One
module F = Make
module ArgAlias = A
module Aliased = F (ArgAlias)

let forward_alias (root : One.t) (x : One.t) = Again.remember root x
(*@ forward_alias root x requires Alias.live root
    requires past (mem x s.cells)
    ensures Aliased.live root
    ensures past (mem x s.cells) *)
