module Abstract : sig
  type t

  val make : int -> t
end = struct
  type t = int

  let make (value : int) = value
end

let fresh value = Abstract.make value
(*@ result = fresh value ensures result + 1 = value *)
