module type Abstract = sig
  type t

  val make : int -> t
  val read : t -> int
end

module Left : Abstract = struct
  type t = int

  let make (value : int) = value
  let read (value : t) = value
end

module Right : Abstract = struct
  type t = int

  let make (value : int) = value
  let read (value : t) = value
end

let mix value = Right.read (Left.make value)
