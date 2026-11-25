module type KEY = sig
  type t

  val hash : t -> int
  (*@ result = hash x pure ensures 0 <= result *)
end

module Make (Key : KEY) = struct
  let repeated x = Key.hash x = Key.hash x
end

module Integer_key = struct
  type t = int

  let hash (x : int) = if x >= 0 then x else 0
  (*@ result = hash x ensures 0 <= result *)
end

module Integers = Make (Integer_key)

let client () =
  let _ = Mutex.create () in
  assert (Integers.repeated 42)

module type ORDINARY = sig
  type t

  val hash : t -> int
  (*@ result = hash x ensures 0 <= result *)
end

module Ordinary (Key : ORDINARY) = struct
  let use x = Key.hash x
end

module Forward_key = struct
  type t = int

  let hash (x : int) = if x >= 0 then x else 0
  (*@ result = hash x ensures 0 <= result *)
end

module Ordinary_first = Ordinary (Forward_key)
module Pure_after = Make (Forward_key)

module Reverse_key = struct
  type t = int

  let hash (x : int) = if x >= 0 then x else 0
  (*@ result = hash x ensures 0 <= result *)
end

module Pure_first = Make (Reverse_key)
module Ordinary_after = Ordinary (Reverse_key)

let mixed_views () =
  assert (0 <= Ordinary_first.use 42);
  assert (Pure_after.repeated 42);
  assert (Pure_first.repeated 42);
  assert (0 <= Ordinary_after.use 42)
