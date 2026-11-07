module type View = sig
  type t

  val identity : t -> t
  (*@ result = identity x ensures result === x *)
end

module Make () = struct
  type t = Value of int

  let identity (x : t) = x
end

module First : View = Make ()
module Second : View = Make ()
module Alias = First

let forward (x : First.t) = Alias.identity x
(*@ result = forward x ensures result === x *)

let second (x : Second.t) = Second.identity x
(*@ result = second x ensures result === x *)
