module Make () = struct
  exception Empty

  let read (cell : int option Atomic.t) =
    match Atomic.get cell with None -> raise Empty | Some value -> value
end

module First = Make ()
module Second = Make ()

let first_or cell = try First.read cell with Second.Empty -> 7 | First.Empty -> 0
(*@ result = first_or cell
    requires own cell None
    ensures own cell None && result = 0 *)

let second_or cell = try Second.read cell with First.Empty -> 7 | Second.Empty -> 0
(*@ result = second_or cell
    requires own cell None
    ensures own cell None && result = 0 *)
