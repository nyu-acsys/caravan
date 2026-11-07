module type Argument = sig end

module Argument = struct end

module Inner (X : Argument) = struct
  type t = Value of int

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module Outer (X : Argument) = struct
  module Nested = Inner (X)

  let identity (x : Nested.t) = Nested.identity x
  (*@ result = identity x ensures result === x *)

  module Captured (Y : Argument) = struct
    type t = { value : int }

    let identity (x : t) = x
    (*@ result = identity x ensures result = x *)
  end
end

module Direct = Inner (Argument)
module Left = Outer (Argument)
module Right = Outer (Argument)
module First_captured = Left.Captured (Argument)
module Second_captured = Right.Captured (Argument)

let nested () =
  match Right.identity (Left.identity (Direct.Value 7)) with
  | Direct.Value x -> assert (x = 7)

let captured () =
  let x = Second_captured.identity { First_captured.value = 7 } in
  assert (x.Second_captured.value = 7)

let application_path (x : Outer(Argument).Nested.t) = Direct.identity x
(*@ result = application_path x ensures result = x *)
