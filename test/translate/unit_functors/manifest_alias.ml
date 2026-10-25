module Shared = struct
  type t = Value of int
end

module Make () = struct
  type t = Shared.t

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module First = Make ()
module Second = Make ()

let check () =
  let value = Second.identity (First.identity (Shared.Value 7)) in
  match value with Shared.Value n -> assert (n = 7)
