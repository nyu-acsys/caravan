type 'a t = { values : 'a list }

let empty () = { values = [] }
(*@ result = empty () pure ensures result === { values = [] } *)

let empty_client () =
  let integers : int t = empty () in
  let booleans : bool t = empty () in
  assert (integers.values = []);
  assert (booleans.values = [])
