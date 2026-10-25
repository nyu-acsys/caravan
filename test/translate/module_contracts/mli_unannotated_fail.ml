module type S = sig
  val f : int -> int
  (*@ result = f x requires x >= 0 ensures result = x *)
end

module Actual_local = struct
  let f (x : int) = x
  (*@ result = f x requires x >= 0 ensures result = x *)
end

module Checked : S = Actual_local
