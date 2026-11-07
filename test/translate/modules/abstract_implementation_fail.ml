module Abstract : sig
  type t

  val make : int -> t
end = struct
  type t = int

  let make (value : int) = value
end

let increment (value : Abstract.t) = value + 1
