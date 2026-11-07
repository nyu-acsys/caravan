module Make () = struct
  type t = Empty | Value of int

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module Make_alias = Make
module First = Make ()
module Second = Make_alias ()
module Result_alias = First

let check () =
  let first = Result_alias.identity (First.Value 7) in
  let second = Second.identity (Second.Value 9) in
  match (first, second) with
  | First.Value x, Second.Value y -> assert (x = 7 && y = 9)
  | First.Empty, _ | _, Second.Empty -> assert false
