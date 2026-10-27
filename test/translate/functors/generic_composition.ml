module type Value = sig
  type t = Actual.First.t

  val identity : t -> t
  (*@ result = identity x ensures result === x *)
end

module Actual_local = struct
  type t = Actual.First.t

  let identity (x : t) = x
  (*@ result = identity x ensures result === x *)
end

module Make_first (X : Value) = struct
  type t = X.t

  let identity (x : t) = X.identity x
  (*@ result = identity x ensures result === x *)
end

module First = Make_first (Actual_local)

module Make_second (X : Value) = struct
  type t = X.t

  let identity (x : t) = X.identity x
  (*@ result = identity x ensures result === x *)
end

module Second = Make_second (First)
module Checked : Value = First

module type Argument = sig end

module Argument = struct end

module Capture (X : Argument) = struct
  let identity (x : Actual.First.t) = First.identity x
  (*@ result = identity x ensures result === x *)
end

module Captured = Capture (Argument)

let client (x : Actual.First.t) = Second.identity (Checked.identity (Captured.identity x))
(*@ result = client x ensures result === x *)
