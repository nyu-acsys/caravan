module type VALUE = sig
  type t
end

module Make (P : VALUE) = struct
  let id value = value

  (*@ result = id value pure ensures result === value *)
  let alias = id
  let again = alias
end

module First = Make (Modules_extra_value)
module Second = Make (Modules_extra_value)

let integer (value : int) = First.again value
(*@ result = integer value ensures result === value *)

let boolean (value : bool) = Second.alias value
(*@ result = boolean value ensures result === value *)
