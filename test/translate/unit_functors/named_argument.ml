module Factory () = struct
  type t = { mutable contents : int }

  let identity (x : t) = x
  (*@ result = identity x ensures result === x *)
end

module type Argument = sig
  type t

  val identity : t -> t
  (*@ result = identity x ensures result === x *)
end

module Make (X : Argument) = struct
  type t = X.t

  let identity (x : t) = X.identity x
  (*@ result = identity x ensures result === x *)
end

module First = Factory ()
module Second = Factory ()
module First_alias = First
module Left = Make (First)
module Right = Make (First_alias)
module Other = Make (Second)

let check () =
  let first = { First.contents = 7 } in
  let second = { Second.contents = 9 } in
  let first = Right.identity (Left.identity first) in
  let second = Other.identity second in
  assert (first.First.contents = 7 && second.Second.contents = 9)
