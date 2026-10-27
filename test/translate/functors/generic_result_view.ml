module type Argument = sig end

module Argument = struct end

module Make (X : Argument) = struct
  let identity (x : int) = x
  (*@ result = identity x ensures result = x *)
end

module Instance = Make (Argument)

let direct (x : int) = Instance.identity x
(*@ result = direct x ensures result = Instance.identity x *)

module type Identity = sig
  val identity : int -> int
  (*@ result = identity x ensures result = x *)
end

module Checked : Identity = Instance

let client (x : int) = Checked.identity x
(*@ result = client x ensures result = x *)
