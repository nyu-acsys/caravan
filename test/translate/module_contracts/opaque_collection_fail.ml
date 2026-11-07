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
  (*@ result = read x requires own x.contents value ensures own x.contents value && result = value
      ensures forall values: state finset. Finset.mem 0 values <-> Finset.mem 0 values *)
end =
  Actual_local
