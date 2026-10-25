module Make () = struct
  type t = Value of int

  let helper (x : t) = x
  (*@ result = helper x ensures result = x *)

  let identity (x : t) = helper x
  (*@ Ghost.scope (fun invoke -> let result = invoke () in result) *)
  (*@ manual *)
  (*@ result = identity x ensures result = x *)
end

module First = Make ()
module Second = Make ()

let check () =
  match (First.identity (First.Value 7), Second.identity (Second.Value 9)) with
  | First.Value x, Second.Value y -> assert (x = 7 && y = 9)
