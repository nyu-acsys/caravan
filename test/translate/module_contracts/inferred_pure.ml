module Actual_local = struct
  let read (x : int) = x + 1
  (*@ result = read x requires 0 <= x < max_int ensures result >= 0 *)
end

module Checked : sig
  val read : int -> int
  (*@ result = read x requires 0 <= x < max_int ensures result >= 0 *)
end =
  Actual_local

let direct x = Actual_local.read x
(*@ result = direct x requires 0 <= x < max_int ensures result = Actual_local.read x *)

let client x = Checked.read x
(*@ result = client x requires 0 <= x < max_int ensures result >= 0 *)
