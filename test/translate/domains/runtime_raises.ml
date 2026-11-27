exception Failed

let work (cell : int ref) fail =
  cell := 1;
  if fail then raise Failed else 7
(*@ result = work cell fail
    requires own cell.contents 0
    ensures own cell.contents 1 && result === 7
    raises Failed -> own cell.contents 1 *)

let launch cell fail = Domain.spawn (fun () -> work cell fail)
(*@ domain = launch cell fail
    requires own cell.contents 0
    ensures Job.handle domain cell fail *)

let finish (domain : int Domain.t) (cell : int ref) (fail : bool) = Domain.join domain
(*@ result = finish domain cell fail
    requires Job.handle domain cell fail
    ensures own cell.contents 1 && result === 7
    raises Failed -> own cell.contents 1 *)

let client fail =
  let cell = ref 0 in
  let domain = launch cell fail in
  let result = try finish domain cell fail with Failed -> 7 in
  assert (!cell = 1);
  result
(*@ result = client fail ensures result === 7 *)

let loops () =
  try
    while false do
      let cell = ref 0 in
      let domain = launch cell true in
      let result = Domain.join domain in
      ()
    done
  with Failed -> ()
