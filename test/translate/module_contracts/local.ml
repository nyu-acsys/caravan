module Actual_local = struct
  let read (x : int) = x

  (*@ result = read x requires x >= 0 ensures result = x *)
  let touch () = ()
  (*@ touch () ensures true *)
end

module Checked : sig
  val read : int -> int

  (*@ result = read x requires x >= 1 ensures result >= 0 *)
  val touch : unit -> unit
  (*@ touch () ensures true *)
end =
  Actual_local

let client x =
  Checked.touch ();
  Checked.read x
(*@ result = client x requires x >= 1 ensures result >= 0 *)
