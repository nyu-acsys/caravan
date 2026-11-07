module First : sig
  type t
  (*@ predicate related (value : t) (expected [@implicit] : t) *)

  val identity : t -> t
  (*@ result = identity value ensures result === value *)
end

module Second : sig
  type t
  (*@ predicate related (value : t) (expected [@implicit] : t) *)

  val identity : t -> t
  (*@ result = identity value ensures result === value *)
end
