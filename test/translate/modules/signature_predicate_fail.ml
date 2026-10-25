module Container : sig
  type t

  (*@ predicate holds (value : t) *)

  val identity : t -> t
end = struct
  type t = int

  let identity (value : t) = value
end
