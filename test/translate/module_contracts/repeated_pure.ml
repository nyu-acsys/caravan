module Actual_local = struct
  let read (x : int) = x + 1
  (*@ result = read x requires 0 <= x < max_int ensures result >= 0 *)
end

module type View = sig
  val read : int -> int
  (*@ result = read x requires 0 <= x < max_int ensures result >= 0 *)
end

module Original : View = Actual_local
module Repeated : View = Actual_local
module Checked : View = Original

let direct x = Actual_local.read x
(*@ result = direct x requires 0 <= x < max_int ensures result = Actual_local.read x *)

let client x =
  let first = Original.read x in
  let second = Repeated.read x in
  let third = Checked.read x in
  assert (first >= 0 && second >= 0 && third >= 0)
(*@ client x requires 0 <= x < max_int ensures true *)
