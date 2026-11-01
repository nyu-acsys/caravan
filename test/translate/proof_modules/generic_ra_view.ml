module type INPUT = sig
  (*@ module R : ResourceAlgebra *)
end

module type OUTPUT = sig
  (*@ module R : ResourceAlgebra *)
  type t
  (*@ invariant is_counter (c : t) *)
  (*@ predicate counter (c : t) (n : int) *)
  (*@ predicate model (c : t) (value [@implicit] : R.t) *)

  val create : unit -> t
  (*@ c = create () ensures is_counter c && counter c 0 && model c R.id *)

  val set_one : t -> unit
  (*@ atomic set_one c requires is_counter c
      atomic requires counter c n && model c R.id
      atomic ensures counter c 1 && model c R.id && n = 0 *)

  val read : t -> int
  (*@ result = atomic read c requires is_counter c
      atomic requires counter c n && model c R.id
      atomic ensures counter c n && model c R.id && result = n *)
end

module A = struct end
module B = struct end
module C = struct end

module Make (X : INPUT) : OUTPUT = struct
  type t = int Atomic.t

  let create () = Atomic.make 0
  (*@ initially { value = 0; model = X.R.id } *)

  let rec set_one c =
    if Atomic.compare_and_set c 0 1 (*@ performs set_one *) then () else set_one c

  let read (c : t) = Atomic.get c (*@ commit *)
end

module One = Make (A)
module Two = Make (B)
module Again = Make (A)
module Alias = One
module Three = Make (C)

let sum2 () =
  let first = One.create () in
  let second = Two.create () in
  One.set_one first;
  Two.set_one second;
  Alias.read first + Two.read second
(*@ result = sum2 () ensures result = 2 *)

let repeated () =
  let first = Again.create () in
  Again.set_one first;
  Again.read first
(*@ result = repeated () ensures result = 1 *)

let custom () =
  let c = Three.create () in
  Three.set_one c;
  Three.read c
(*@ result = custom () ensures result = 1 *)
