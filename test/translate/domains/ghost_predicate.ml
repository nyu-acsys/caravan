module Worker = struct
  let valid (value : int) = value = 7
  (*@ result = valid value pure ensures result = (value = 7) *)

  let work (cell : int ref) = !cell
  (*@ Ghost.returns (fun result () -> result) *)
  (*@ manual *)
  (*@ result, [seen : int] = work [expected : int] cell
      requires own cell.contents expected && valid expected && approved expected
        && allowed expected && accepted expected
      ensures own cell.contents expected && result = seen && seen = expected *)
end

let client () =
  let cell = ref 7 in
  let domain =
    Domain.spawn (fun () -> Worker.work cell)
    (*@ Ghost.scope (fun invoke ->
        fold Worker.accepted 7;
        let domain = invoke 7 in
        domain) *)
  in
  let result =
    Domain.join domain
    (*@ Ghost.scope (fun invoke ->
        let (result, seen) = invoke () in
        assert (result = seen && seen = 7);
        result) *)
  in
  assert (!cell = 7);
  result
(*@ manual *)
(*@ result = client () ensures result = 7 *)
