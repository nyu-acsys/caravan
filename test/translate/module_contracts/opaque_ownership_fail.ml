module Actual_local = struct
  type state = int
  type cell = state ref

  let read (x : cell) (n : int) = !x
  (*@ result = read x n requires own x.contents n ensures own x.contents n && result = n *)
end

module Checked : sig
  type state
  type cell = state ref

  val read : cell -> int -> state
  (*@ result = read x n requires own x.contents n ensures own x.contents n *)
end =
  Actual_local
