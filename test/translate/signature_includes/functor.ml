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

module Make (Cell : Extended) = struct
  let read_twice x =
    let first = Cell.read x in
    let second = Cell.again x in
    assert (first = second);
    second
  (*@ result = read_twice x requires Cell.owned x n && Cell.shared x ensures Cell.owned x n && Cell.shared x && result = n *)
end

module Instance = Make (Resource_actual)

let client x = Instance.read_twice x
(*@ result = client x requires Resource_actual.owned x n && Resource_actual.shared x ensures Resource_actual.owned x n && Resource_actual.shared x && result = n *)
