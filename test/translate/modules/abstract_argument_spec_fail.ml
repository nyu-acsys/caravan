module Abstract : sig
  type t

  val make : int -> t
end = struct
  type t = int

  let make (value : int) = value
end

let identity (value : Abstract.t) = value
(*@ result = identity value ensures value + 1 = result *)
