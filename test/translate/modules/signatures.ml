module type Integer = sig
  type t = int

  val identity : t -> t
  (*@ result = identity value ensures result = value *)
end

module type Boolean = sig
  val identity : bool -> bool
  (*@ result = identity value ensures result = value *)
end

module Outer = struct
  module Inner : Integer = struct
    type t = int

    let identity value = value
  end

  module Flag : Boolean = struct
    let identity value = value
  end

  let integer value = Inner.identity value
  (*@ result = integer value ensures result = value *)

  let boolean value = Flag.identity value
  (*@ result = boolean value ensures result = value *)
end

module Abstract : sig
  type t

  val make : int -> t
  val identity : t -> t
  (*@ result = identity value ensures result = value *)
end = struct
  type t = int

  let make (value : int) = value
  let identity value = value
end

let abstract_identity (value : Abstract.t) = Abstract.identity value
(*@ result = abstract_identity value ensures result = value *)
