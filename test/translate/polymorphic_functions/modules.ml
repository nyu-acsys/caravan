module Identity = struct
  let id value = value
  (*@ result = id value pure ensures result === value *)
end

module type VALUE = sig
  type t

  val keep : t -> t
  (*@ result = keep value ensures result === value *)
end

module Integer = struct
  type t = int

  let keep (value : t) = value
  (*@ result = keep value ensures result === value *)
end

module Boolean = struct
  type t = bool

  let keep (value : t) = value
  (*@ result = keep value ensures result === value *)
end

module Make (P : VALUE) = struct
  let pair (value : P.t) other = (value, other)
  (*@ result = pair value other pure ensures result === (value, other) *)
end

module Integers = Make (Integer)
module Booleans = Make (Boolean)

let integer (value : int) = Integers.pair (Identity.id value) true
(*@ result = integer value ensures result === (value, true) *)

let boolean (value : bool) = Booleans.pair (Identity.id value) 17
(*@ result = boolean value ensures result === (value, 17) *)

let alternate (value : int) = Integers.pair value 42
(*@ result = alternate value ensures result === (value, 42) *)

let logical_clients (value : int) (flag : bool) = ()
(*@ logical_clients value flag
    ensures Identity.id value === value
    ensures Identity.id flag === flag
    ensures Integers.pair value flag === (value, flag)
    ensures Booleans.pair flag value === (flag, value) *)
