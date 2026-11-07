module type Base = sig
  type t

  (*@ predicate owned (x : t) (n [@implicit] : int) *)
  (*@ invariant shared (x : t) *)

  val read : t -> int
  (*@ result = read x requires owned x n && shared x ensures owned x n && shared x && result = n *)
end

module type Extended = sig
  include Base

  val again : t -> int
  (*@ result = again x requires owned x n && shared x ensures owned x n && shared x && result = n *)
end

module Checked : Extended = Resource_actual

let client x =
  let first = Checked.read x in
  let second = Checked.again x in
  assert (first = second);
  second
(*@ result = client x requires Checked.owned x n && Checked.shared x ensures Checked.owned x n && Checked.shared x && result = n *)
