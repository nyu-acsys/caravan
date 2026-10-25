module type Argument = sig end

module First_argument = struct end
module Second_argument = struct end

module Make (X : Argument) = struct
  type value = Value of int
  type cell = { mutable contents : int }

  let identity (x : value) = x
  (*@ result = identity x ensures result = x *)
end

module First = Make (First_argument)
module Second = Make (Second_argument)

let check () =
  let a = { First.contents = 0 } in
  let b = { Second.contents = 1 } in
  a.First.contents <- 7;
  assert (b.Second.contents = 1);
  match (First.identity (First.Value 7), Second.identity (Second.Value 9)) with
  | First.Value x, Second.Value y -> assert (x = 7 && y = 9)
