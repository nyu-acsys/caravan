exception Failed

let work (cell : int ref) fail =
  cell := 1;
  if fail then raise Failed;
  7
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [seen : int] = work cell fail
    requires own cell.contents 0
    ensures own cell.contents 1 && result = seen && seen = 7
    raises Failed -> own cell.contents 1 *)

let client fail =
  let cell = ref 0 in
  let domain = Domain.spawn (fun () -> work cell fail) in
  let result =
    try
      Domain.join domain
      (*@ Ghost.scope (fun invoke ->
          let (result, seen) = invoke () in
          assert (result = seen && seen = 7);
          assert (own cell.contents 1);
          result) *)
    with Failed ->
      assert (!cell = 1);
      7
  in
  assert (!cell = 1);
  result
(*@ manual *)
(*@ result = client fail ensures result = 7 *)
