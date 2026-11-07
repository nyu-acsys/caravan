module type VALUE = sig
  type t
end

module Integer = struct
  type t = int
end

module Make (P : VALUE) = struct
  type 'a marker = Marker of 'a

  let keep (fixed : P.t) value =
    let step () = (fixed, value) in
    (*@ result = step () ensures result === (fixed, value) *)
    step ()
  (*@ result = keep fixed value ensures result === (fixed, value) *)
end

module First = Make (Integer)
module Second = Make (Integer)
module Alias = First

let integer () =
  let fixed, value = Alias.keep 17 23 in
  assert (fixed = 17);
  assert (value = 23)

let boolean () =
  let fixed, value = Second.keep 42 true in
  assert (fixed = 42);
  assert value
