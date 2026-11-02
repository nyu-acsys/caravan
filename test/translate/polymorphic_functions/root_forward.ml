module type VALUE = sig
  type t
end

let id value = value
(*@ result = id value pure ensures result === value *)

module Make (P : VALUE) = struct
  let pair (value : P.t) other = (id value, other)
  (*@ result = pair value other pure ensures result === (value, other) *)

  let ready () = true
  (*@ result = ready () pure ensures result *)
end

module First = Make (Modules_extra_value)

let forward (value : Modules_extra_value.t) other = First.pair value other
(*@ result = forward value other pure ensures result === (value, other) *)

let twice (value : Modules_extra_value.t) other = forward value other
(*@ result = twice value other pure ensures result === (value, other) *)

let checked value = if First.ready () then value else value
(*@ result = checked value pure ensures result === value *)

module Capture (P : VALUE) = struct
  let forward (value : Modules_extra_value.t) other = twice value other
  (*@ result = forward value other pure ensures result === (value, other) *)
end

module Captured = Capture (Modules_extra_value)

let boolean (value : Modules_extra_value.t) = Captured.forward value true
(*@ result = boolean value ensures result === (value, true) *)

let integer (value : int) = checked value
(*@ result = integer value ensures result === value *)
