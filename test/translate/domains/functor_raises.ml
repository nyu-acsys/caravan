module Worker () = struct
  exception Failed

  let work fail = if fail then raise Failed else 1
  (*@ result = work fail
      ensures result === 1
      raises Failed -> true *)

  let launch fail = Domain.spawn (fun () -> work fail)
  (*@ domain = launch fail ensures Job.handle domain fail *)

  let finish (domain : int Domain.t) (fail : bool) = Domain.join domain
  (*@ result = finish domain fail
      requires Job.handle domain fail
      ensures result === 1
      raises Failed -> true *)

  let client fail =
    let domain = launch fail in
    try finish domain fail with Failed -> 1
  (*@ result = client fail ensures result === 1 *)
end

module First = Worker ()
module Second = Worker ()

let client () = Second.client true
(*@ result = client () ensures result === 1 *)

let direct () =
  let domain = Domain.spawn (fun () -> Second.work true) in
  try Domain.join domain with Second.Failed -> 1
(*@ result = direct () ensures result === 1 *)
