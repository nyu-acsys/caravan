module type INPUT = sig end

module type OUTPUT = sig
  type t
  (*@ invariant is_counter (c : t) *)

  val create : unit -> t
  (*@ c = create () ensures is_counter c *)
end

module A = struct end

module Make (X : INPUT) : OUTPUT = struct
  type t = int Atomic.t

  let create () = Atomic.make 0
  (*@ initially { value = 0 } *)
end

module One = Make (A)
module Outside = struct end
