module type Identity = sig
  type t

  val identity : t -> t
  (*@ result = identity value ensures result = value *)
end

module type Extended = sig
  include Identity

  val again : t -> t
  (*@ result = again value ensures result = value *)
end

module Integer : Extended = struct
  type t = int

  let identity value = value
  let again value = value
end

module Boolean : Extended = struct
  type t = bool

  let identity value = value
  let again value = value
end

let integer (value : Integer.t) = Integer.again (Integer.identity value)
(*@ result = integer value ensures result = value *)

let boolean (value : Boolean.t) = Boolean.again (Boolean.identity value)
(*@ result = boolean value ensures result = value *)
