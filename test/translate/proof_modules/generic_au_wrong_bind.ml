module type INPUT = sig
  val identity : int -> int
  (*@ result = identity value ensures result = value *)
end

module A = struct
  let identity (value : int) = value
  (*@ result = identity value ensures result = value *)
end

module B = struct
  let identity (value : int) = value
  (*@ result = identity value ensures result = value *)
end

module Make (X : INPUT) = struct
  let read (value : int) = X.identity value
  (*@ Ghost.scope (fun step ->
      let token = Read.bind () in
      let result = step () in
      Read.access token value;
      Read.commit token value result;
      result) *)
  (*@ manual *)
  (*@ result = atomic read value
      atomic ensures result = value *)

  let other (value : int) = X.identity value
  (*@ Ghost.scope (fun step ->
      let token = Read.bind () in
      let result = step () in
      result) *)
  (*@ manual *)
  (*@ result = atomic other value
      atomic ensures result = value *)
end

module One = Make (A)
module Two = Make (B)
module Again = Make (A)
module Alias = One
module F = Make
module ArgAlias = A
module Aliased = F (ArgAlias)

let use_one (value : int) = One.read value
(*@ result = use_one value ensures result = value *)

let use_two (value : int) = Two.read value
(*@ result = use_two value ensures result = value *)
