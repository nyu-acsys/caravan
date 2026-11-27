val out_of_bounds : unit -> int
val negative : unit -> bool array
val unowned : int array -> unit
(*@ unowned a requires 0 < Array.length a *)
