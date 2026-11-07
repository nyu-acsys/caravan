module type Value = sig
  type t

  val identity : t -> t
  (*@ result = identity x ensures result === x *)
end

module Integers = struct
  type t = int

  let identity (x : t) = x
  (*@ result = identity x ensures result === x *)
end

module Booleans = struct
  type t = bool

  let identity (x : t) = x
  (*@ result = identity x ensures result === x *)
end

module Outer (X : Value) = struct
  module Make (Y : Value) (Z : Value) = struct
    type t = Pair of X.t * Y.t

    let capture x y = Pair (X.identity x, Y.identity y)
    (*@ result = capture x y ensures result === Pair (x, y) *)

    let last (x : Z.t) = Z.identity x
    (*@ result = last x ensures result === x *)
  end
end

module Scope = Outer (Integers)
module With_integer = Scope.Make (Integers)
module With_boolean = Scope.Make (Booleans)
module Integer = With_integer (Booleans)
module Boolean = With_boolean (Integers)

let check () =
  begin match Integer.capture 7 9 with Integer.Pair (x, y) -> assert (x = 7 && y = 9)
  end;
  begin match Boolean.capture 11 true with Boolean.Pair (x, y) -> assert (x = 11 && y)
  end;
  assert (Integer.last true);
  assert (Boolean.last 13 = 13)
