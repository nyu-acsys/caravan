module type ARGUMENT = sig
  val identity : int -> int
  (*@ result = identity value ensures result = value *)
end

module A = struct
  let identity (value : int) = value
  (*@ result = identity value ensures result = value *)
end

module B = A

module Make (X : ARGUMENT) (Y : ARGUMENT) = struct
  let identity (value : int) = X.identity (Y.identity value)
  (*@ result = identity value ensures result = value *)
end

module Earlier = Make (A)
module Later = Make (A)
module First = Later (B)
module Second = Earlier (B)

let check (value : int) = Second.identity (First.identity value)
(*@ result = check value ensures result = value *)
