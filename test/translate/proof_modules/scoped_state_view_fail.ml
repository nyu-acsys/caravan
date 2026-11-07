module Counter : sig
  type t
  (*@ invariant is_counter (c : t) *)
  (*@ predicate counter (c : t) (n : int) *)
end = struct
  type t = int Atomic.t
end
