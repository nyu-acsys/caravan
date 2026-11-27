module type KEY = sig
  type t
end

module Make (Key : KEY) : sig
  val keep : Key.t -> Key.t
  (*@ result = keep x ensures result === x *)
end = struct
  let keep (x : Key.t) = x
end

module Integer = struct
  type t = int
end

module First = Make (Integer)
module Second = Make (Integer)

module Native = struct
  let keep (x : int) = x
  (*@ result = keep x ensures result === x *)

  let fresh (x : int) = x
end

let client x =
  let y = First.keep x in
  let z = Second.keep y in
  Native.keep z
