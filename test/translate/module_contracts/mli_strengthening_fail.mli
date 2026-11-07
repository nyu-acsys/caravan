module Checked : sig
  val f : int -> int
  (*@ result = f x ensures result = x + 1 *)
end
