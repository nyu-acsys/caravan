(*@ invariant stable (value : int) *)

val make : int -> int [@@caravan.local]
(*@ result = make value
    ensures result = value && stable result *)

val no_step : unit -> unit [@@caravan.local]
(*@ result = no_step ()
    ensures result = () *)
