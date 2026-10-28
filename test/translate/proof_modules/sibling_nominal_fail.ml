module type VIEW = sig
  type t

  (*@ predicate held (x : t) *)
end

module Left : VIEW = struct
  type t = int Atomic.t
end

module Right : VIEW = struct
  type t = int Atomic.t
end
