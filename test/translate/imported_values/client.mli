val pair : unit -> int Constants.t * int Constants.t
(*@ result = pair ()
    ensures match result with (first, second) ->
      first === second && Constants.stable first && Constants.stable second *)

val number : unit -> int
(*@ result = number ()
    ensures result = 0 *)

val unit_value : unit -> unit
(*@ result = unit_value ()
    ensures result = () *)

val local_value : unit -> int
(*@ result = local_value ()
    ensures result = 17 && Operations.stable result *)

val inspect : int Atomic.t -> int
(*@ result = atomic inspect cell
    atomic requires own cell value
    atomic ensures own cell value && result = value *)
