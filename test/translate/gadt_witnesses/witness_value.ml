type ('a, _) poly = Option : ('a, 'a option) poly | Value : ('a, 'a) poly

let get : type a r. a -> (a, r) poly -> r =
 fun x poly -> match poly with Option -> Some x | Value -> x

let use (x : int) =
  let w = Option in
  get x w
