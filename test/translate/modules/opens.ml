module Original = struct
  type cell = { mutable value : int }

  let identity (value : int) = value
  (*@ result = identity value ensures result = value *)

  let get (c : cell) = c.value
  (*@ result = get c
      requires own c.value v
      ensures own c.value v && result = v *)
end

module Opened = struct
  open Original

  let call value = identity value
  (*@ result = call value ensures result = value *)

  let read (c : cell) = get c
  (*@ result = read c requires full c ensures full c *)
end

module Sealed : sig
  open Original

  val read : cell -> int
end = struct
  include Opened
end

module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x n ensures counter x n && result = n *)
end

module Make (Cell : View) = struct
  open Cell

  let read x = read x
  (*@ result = read x requires counter x n ensures counter x n && result = n *)
end

open Opened

let client (c : Original.cell) = read c + call 1
(*@ result = client c requires Original.full c ensures Original.full c *)
