module type KEY = sig
  type t

  val equal : t -> t -> bool
  (*@ result = equal x y pure ensures result === (x === y) *)

  val hash : t -> int
  (*@ result = hash x pure ensures 0 <= result *)
end

module Make (Key : KEY) = struct
  let repeated x = Key.hash x = Key.hash x
  let same x y = Key.equal x y
end

module Integer_key = struct
  type t = int

  let equal (x : int) y = x = y
  let hash (x : int) = if x >= 0 then x else 0
end

module Integers = Make (Integer_key)

let client () =
  assert (Integers.repeated 42);
  assert (Integers.same 42 42);
  assert (not (Integers.same 42 43))

module Forward (Key : KEY) = struct
  module Set = Make (Key)

  let repeated x = Set.repeated x
end

module Forwarded = Forward (Integer_key)

let forwarded () = assert (Forwarded.repeated 42)
