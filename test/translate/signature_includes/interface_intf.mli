module type S = sig
  type t

  val identity : t -> t
  (*@ result = identity value ensures result = value *)
end
