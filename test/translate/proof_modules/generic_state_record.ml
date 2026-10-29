module type INPUT = sig end

module type OUTPUT = sig
  type t
  (*@ invariant is_counter (c : t) *)
  (*@ predicate counter (c : t) (n : int) *)

  val create : unit -> t
  (*@ c = create () ensures is_counter c && counter c 0 *)
end

module A = struct end
module B = struct end

module Make (X : INPUT) : OUTPUT = struct
  type t = { mutable value : int }

  let create () = { value = 0 }
  (*@ initially { value = 0 } *)
end

module One = Make (A)
module Two = Make (B)

let first () = One.create ()
(*@ result = first () ensures One.is_counter result && One.counter result 0 *)

let second () = Two.create ()
(*@ result = second () ensures Two.is_counter result && Two.counter result 0 *)
