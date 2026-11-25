module Cell : sig
  type t = int Atomic.t

  (*@ invariant root (cell : t) *)
  (*@ invariant leaf (cell : t) *)
end = struct
  type t = int Atomic.t
end
