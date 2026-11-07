module type INPUT = sig end

module type OUTPUT = sig
  type t = int Atomic.t
  (*@ invariant is_counter (c : t) *)

  val create : unit -> t
  (*@ c = create () ensures is_counter c *)

  val set_one : t -> unit
  (*@ atomic set_one c requires is_counter c
      atomic ensures is_counter c *)
end

module A = struct end

module Make (X : INPUT) : OUTPUT = struct
  type t = int Atomic.t

  let create () = Atomic.make 0
  (*@ initially { value = 0 } *)

  let rec set_one c =
    if Atomic.compare_and_set c 0 1 (*@ performs set_one *) then () else set_one c
end

module One = Make (A)

let try_action (c : One.t) = Atomic.compare_and_set c 0 1
(*@ performs set_one *)
(*@ result = try_action c requires One.is_counter c ensures One.is_counter c *)
