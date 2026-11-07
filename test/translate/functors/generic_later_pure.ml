module type Argument = sig end

module First_argument = struct end
module Second_argument = struct end

module Make (X : Argument) = struct
  let sibling (x : int) = x
  let ( +. ) (x : int) (_y : int) = sibling x
  let helper (x : int) = x +. 0
end

module First = Make (First_argument)
module Second = Make (Second_argument)

let first (x : int) = First.helper x
let second (x : int) = Second.helper x
(*@ result = second x ensures result = Second.helper x && result = x *)
