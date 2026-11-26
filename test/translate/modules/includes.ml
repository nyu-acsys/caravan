module Original = struct
  type cell = { mutable value : int }

  let get (c : cell) = c.value
  (*@ result = get c
      requires own c.value v
      ensures own c.value v && result = v *)
end

module Extended = struct
  include Original

  let peek (c : cell) = get c
end

module type Element = sig
  type t
end

module Make (A : Element) = struct
  let same (value : A.t) = value
  (*@ result = same value ensures result === value *)
end

module Int = struct
  type t = int
end

module Ints = struct
  include Make (Int)

  let again (value : int) = same value
  (*@ result = again value ensures result = value *)
end

module Inline = struct
  include struct
    let hidden (value : int) = value
    (*@ result = hidden value ensures result = value *)
  end

  let call (value : int) = hidden value
  (*@ result = call value ensures result = value *)
end

let client (c : Extended.cell) = Extended.peek c + Ints.same 3 + Inline.hidden 4
(*@ result = client c
    requires Extended.full c
    ensures Extended.full c *)
