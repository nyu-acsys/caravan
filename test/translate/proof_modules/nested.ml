module type VIEW = sig
  type t

  (*@ invariant zero (x : t) *)

  val read : t -> int
  (*@ result = read x requires zero x ensures zero x && result = 0 *)
end

module Outer : sig
  module Inner : VIEW
  module Alias = Inner
end = struct
  module Inner = struct
    type t = int Atomic.t

    let read (x : t) = Atomic.get x
  end

  module Alias = Inner
end

module External = Outer.Inner

let read_nested x = Outer.Inner.read x
(*@ result = read_nested x
    requires Outer.Inner.zero x
    ensures Outer.Inner.zero x && result = 0 *)

let read_alias x = Outer.Alias.read x
(*@ result = read_alias x
    requires Outer.Alias.zero x
    ensures Outer.Alias.zero x && result = 0 *)

let read_external x = External.read x
(*@ result = read_external x
    requires External.zero x
    ensures External.zero x && result = 0 *)
