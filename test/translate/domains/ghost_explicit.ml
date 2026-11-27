let work (cell : int ref) = !cell
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [seen : int] = work [expected : int] cell
    requires own cell.contents expected
    ensures own cell.contents expected && result = seen && seen = expected *)

let client () =
  let cell = ref 7 in
  let domain =
    Domain.spawn (fun () -> work cell)
    (*@ Ghost.scope (fun invoke ->
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

let launch (cell : int ref) = Domain.spawn (fun () -> work cell)
(*@ Ghost.scope (fun invoke ->
    let domain = invoke 7 in
    domain) *)
(*@ manual *)
(*@ domain = launch cell
    requires own cell.contents 7
    ensures Job.handle domain cell 7 *)

let finish (domain : int Domain.t) (cell : int ref) = Domain.join domain
(*@ Ghost.scope (fun invoke ->
    let (result, seen) = invoke () in
    assert (result = seen && seen = 7);
    result) *)
(*@ manual *)
(*@ result = finish domain cell
    requires Job.handle domain cell 7
    ensures own cell.contents 7 && result = 7 *)

let helper_client () =
  let cell = ref 7 in
  let domain = launch cell in
  let result = finish domain cell in
  assert (!cell = 7);
  result
(*@ result = helper_client () ensures result = 7 *)
