module type KEY = sig
  type t

  val hash : t -> int
  (*@ result = hash x pure ensures 0 <= result *)
end

module Make (Key : KEY) = struct
  let hash x = Key.hash x
end

module Mutable_key = struct
  type t = int Atomic.t

  let hash (cell : t) = Atomic.get cell
end

module Invalid = Make (Mutable_key)
