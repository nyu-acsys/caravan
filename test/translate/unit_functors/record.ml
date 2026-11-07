module Make () = struct
  type t = { value : int }

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module First = Make ()
module Second = Make ()
module Alias = First

let check () =
  let first = Alias.identity { First.value = 7 } in
  let second = Second.identity { Second.value = 9 } in
  assert (first.First.value = 7 && second.Second.value = 9)
