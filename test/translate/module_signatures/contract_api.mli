(*@ predicate number (value : int) *)

module type Identity = sig
  val identity : int -> int
  (*@ result = identity value ensures result = value *)
end
