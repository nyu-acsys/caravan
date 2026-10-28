module Counter : sig
  type t
  (*@ invariant is_counter (c : t) *)
  (*@ predicate counter (c : t) (n : int) *)

  val create : unit -> t

  (*@ c = create () ensures is_counter c && counter c 0 *)
  val set_one : t -> unit
  (*@ atomic set_one c requires is_counter c
      atomic requires counter c n
      atomic ensures counter c 1 && n = 0 *)
end = struct
  type t = int Atomic.t

  let create () = Atomic.make 0
  (*@ initially { value = 0 } *)

  let rec set_one c = if Atomic.compare_and_set c 0 0 then () else set_one c
end
