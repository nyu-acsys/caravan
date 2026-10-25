module Actual_local = struct
  type state = int
  type cell = state ref

  let read (x : cell) = !x
  (*@ result = read x requires own x.contents value ensures own x.contents value && result = value *)
end

module Checked : sig
  type state
  type cell = state ref

  val read : cell -> state
  (*@ result = read x requires own x.contents value ensures own x.contents value && result = value *)
end =
  Actual_local
