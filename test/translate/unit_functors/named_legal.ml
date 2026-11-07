module Factory () = struct
  type t = int

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module type Argument = sig
  val identity : int -> int
  (*@ result = identity x ensures result = x *)
end

module Actual = struct
  let identity (x : int) = x
  (*@ result = identity x ensures result = x *)
end

module Make (X : Argument) = struct
  module Instance = Factory ()

  let identity x = Instance.identity (X.identity x)
  (*@ result = identity x ensures result = x *)
end

module Instance = Make (Actual)

let check () = assert (Instance.identity 7 = 7)
