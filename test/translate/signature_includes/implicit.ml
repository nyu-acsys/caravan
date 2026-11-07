module type Base = sig
  type t

  (*@ predicate chosen (x : t) (copy [@implicit] : t) *)

  val get : t -> t
  (*@ result = get x requires chosen x copy ensures chosen x copy && result === copy *)
end

module type Extended = sig
  include Base

  val again : t -> t
  (*@ result = again x requires chosen x copy ensures chosen x copy && result === copy *)
end

module Checked : Extended = Implicit_actual

let client x =
  let first = Checked.get x in
  let second = Checked.again x in
  (first, second)
(*@ result = client x requires Checked.chosen x copy ensures Checked.chosen x copy && result === (copy, copy) *)
