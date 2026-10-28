module type VIEW = sig
  type t

  (*@ predicate held (x : t) *)
end

module Box : VIEW = struct
  type t = int Atomic.t
end
