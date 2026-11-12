type ('a, 'b) phantom = Pack of { mutable value : 'b }

let local (value : int) =
  let wrapped : (bool, int) phantom = Pack { value } in
  match wrapped with
  | Pack record ->
      record.value <- value;
      record.value
(*@ result = local value ensures result === value *)

type choice = First of { mutable value : int } | Second of { mutable value : bool }

let independent () =
  let first = First { value = 42 } in
  let second = Second { value = false } in
  match (first, second) with
  | First left, Second right ->
      right.value <- true;
      assert (left.value = 42 && right.value)
  | _ -> assert false
