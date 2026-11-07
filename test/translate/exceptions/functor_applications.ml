(* Each application of a functor declares its own exceptions. *)

module Make () = struct
  type cell = { mutable value : int }

  exception Empty

  let take (c : cell) = if c.value = 0 then raise Empty else c.value
  (*@ r = take c
      requires own c.value v
      ensures own c.value v && v <> 0 && r = v
      raises Empty -> own c.value v && v = 0 *)

  let take_or_zero (c : cell) = try take c with Empty -> 0
  (*@ r = take_or_zero c
      requires own c.value v
      ensures own c.value v && r = v *)
end

module First = Make ()
module Second = Make ()

(* Second's handler does not catch First's exception. *)
let first_or (c : First.cell) =
  try First.take c with Second.Empty -> 7 | First.Empty -> 0
(*@ r = first_or c
    requires own c.value v
    ensures own c.value v && r = v *)
