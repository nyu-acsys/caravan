module type S = sig
  val f : int -> int
  (*@ result = f x ensures result = x *)
end

module Actual_local = struct
  let f (x : int) = x
  (*@ result = f x ensures result = x *)
end

module Checked : S = Actual_local
