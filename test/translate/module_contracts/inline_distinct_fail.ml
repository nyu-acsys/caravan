module Actual_local = struct
  let read (x : int) = x
  (*@ result = read x requires x >= 0 ensures result = x *)
end

module Strong : sig
  val read : int -> int
  (*@ result = read x requires x >= 0 ensures result = x *)
end =
  Actual_local

module Narrow : sig
  val read : int -> int
  (*@ result = read x requires x >= 0 ensures result >= 0 *)
end =
  Actual_local

let client () =
  let result = Narrow.read 7 in
  assert (result = 7)
(*@ client () ensures true *)
