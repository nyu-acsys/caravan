exception Failed

let work value fail = if fail then raise Failed else value
(*@ result = work value fail
    ensures result === value
    raises Failed -> true *)

let launch value fail = Domain.spawn (fun () -> work value fail)
(*@ domain = launch value fail ensures Job.handle domain value fail *)

let finish (domain : 'a Domain.t) (value : 'a) (fail : bool) = Domain.join domain
(*@ result = finish domain value fail
    requires Job.handle domain value fail
    ensures result === value
    raises Failed -> true *)

let client value fail =
  let domain = launch value fail in
  try finish domain value fail with Failed -> value
(*@ result = client value fail ensures result === value *)
