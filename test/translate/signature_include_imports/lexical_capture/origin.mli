module type S = sig
  val identity : int -> int
  (*@ result = identity value
      requires value = bound
      ensures result = value *)
end
