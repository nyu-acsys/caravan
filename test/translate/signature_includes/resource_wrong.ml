module type Base = sig
  type t

  (*@ predicate owned (x : t) (n [@implicit] : bool) *)
  (*@ invariant shared (x : t) *)

  val read : t -> int
end

module type Extended = sig
  include Base

  val again : t -> int
end

module Checked : Extended = Resource_actual
