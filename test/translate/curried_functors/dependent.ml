module type Value = sig
  type t
end

module Integers = struct
  type t = int

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module Make
    (X : Value)
    (Y : sig
      val identity : X.t -> X.t
      (*@ result = identity x ensures result === x *)
    end) =
struct
  type t = Wrap of X.t

  let make x = Wrap (Y.identity x)
  (*@ result = make x ensures result === Wrap x *)
end

module With_integer = Make (Integers)
module First = With_integer (Integers)
module Direct = Make (Integers) (Integers)

let check () =
  match (First.make 7, Direct.make 9) with
  | Direct.Wrap x, First.Wrap y -> assert (x = 7 && y = 9)
