module type KEY = sig
  type t

  val hash : t -> int
  (*@ result = hash x pure ensures 0 <= result *)
end

module Make (Key : KEY) = struct
  let hash x = Key.hash x
end

module Integer_key = struct
  type t = int

  let hash (x : int) = if x >= 0 then x else 0
end

module Integers = Make (Integer_key)
