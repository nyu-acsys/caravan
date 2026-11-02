module type VALUE = sig
  type t

  val keep : t -> t
  (*@ result = keep value ensures result === value *)
end

module Make (P : VALUE) = struct
  let pair (value : P.t) other = (value, other)
  (*@ result = pair value other pure ensures result === (value, other) *)

  let kept (value : P.t) other = (P.keep value, other)
  (*@ result = kept value other ensures result === (value, other) *)
end

module First = Make (Modules_extra_value)
module Again = Make (Modules_extra_value)
module Imported_alias = Modules_extra_value
module Through_alias = Make (Imported_alias)

let boolean (value : Modules_extra_value.t) = First.pair value true
(*@ result = boolean value ensures result === (value, true) *)

let integer (value : Modules_extra_value.t) = Again.pair value 17
(*@ result = integer value ensures result === (value, 17) *)

let integers (value : Modules_extra_value.t) (values : int list) =
  Through_alias.pair value values
(*@ result = integers value values ensures result === (value, values) *)

let forwarded (value : Modules_extra_value.t) (flag : bool) = First.kept value flag
(*@ result = forwarded value flag ensures result === (value, flag) *)
