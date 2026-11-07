module Actual_record = struct
  type t = { mutable value : int }

  let read (x : t) = x.value
  (*@ result = read x
      requires own x.value n
      ensures own x.value n && result = n *)
end

module Checked : sig
  type t = Actual_record.t

  val read : t -> int
  (*@ result = read x
      requires own x.value state && state >= 0
      ensures own x.value state && result >= 0 *)
end =
  Actual_record

let client (cell : Checked.t) = Checked.read cell
(*@ result = client cell
    requires own cell.value state && state >= 0
    ensures own cell.value state && result >= 0 *)
