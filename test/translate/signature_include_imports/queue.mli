include Queue_intf.S
module Left : Queue_intf.S
module Right : Queue_intf.S

include sig
  val answer : unit -> int
  (*@ result = answer () ensures result = 42 *)
end
