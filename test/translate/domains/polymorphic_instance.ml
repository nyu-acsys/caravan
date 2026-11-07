let work value = 3
(*@ result = work value ensures result === 3 *)

let finish (domain : int Domain.t) value = Domain.join domain
(*@ result = finish domain value
    requires Job.handle domain value
    ensures result === 3 *)

let wrong () =
  let domain = Domain.spawn (fun () -> work 7) in
  finish domain true
(*@ result = wrong () ensures result === 3 *)
