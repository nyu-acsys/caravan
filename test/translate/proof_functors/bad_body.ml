module type CELL = sig
  type t

  (*@ predicate counter (cell : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read cell
      requires counter cell n
      ensures counter cell n && result = n *)
end

module Make (Cell : CELL) = struct
  let read (cell : Cell.t) =
    let result =
      Cell.read cell
      (*@ Ghost.scope (fun step ->
          fold wrapped cell;
          preserve cell;
          unfold wrapped cell;
          let result = step () in
          result) *)
    in
    result + 1
  (*@ manual *)
  (*@ result = read cell
      requires Cell.counter cell n
      ensures Cell.counter cell n && result = n *)
end

module First = Make (Actual.First)
module Second = Make (Actual.Second)
