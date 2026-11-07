module First = struct
  type t = int

  let identity (value : t) = value
  (*@ result = identity value
      ensures result = value && forall witness: t. witness = witness *)
end

module Second = struct
  type t = bool

  let identity (value : t) = value
  (*@ result = identity value
      ensures result = value && forall witness: t. witness = witness *)
end

module Third = struct
  let identity (value : int) = First.identity value
  (*@ result = identity value ensures result = value *)
end
