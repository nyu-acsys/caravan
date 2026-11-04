(* Witnesses with several ordinary parameters and various index types. *)

type ('a, 'b, _) pick = First : ('a, 'b, 'a) pick | Second : ('a, 'b, 'b) pick

type (_, _) shape =
  | Items : ('a, 'a list) shape
  | Pair : ('a, 'a * int) shape
  | Count : ('a, int) shape

module Nested = struct
  type (_, _) choice = Keep : ('a, 'a) choice | Drop : ('a, unit) choice
end

let id x = x
