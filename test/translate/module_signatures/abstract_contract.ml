module Abstract : sig
  type t

  val identity : t -> t
  (*@ result = identity value ensures result + 1 = value *)
end = struct
  type t = int

  let identity (value : t) = value
end
