module Worker () = struct
  let work () = 1
  (*@ result = work () ensures result === 1 *)

  let launch () = Domain.spawn work
  (*@ domain = launch () ensures Job.handle domain () *)

  let finish (domain : int Domain.t) = Domain.join domain
  (*@ result = finish domain
      requires Job.handle domain ()
      ensures result === 1 *)

  let client () =
    let domain = launch () in
    finish domain
  (*@ result = client () ensures result === 1 *)
end

module First = Worker ()
module Second = Worker ()

let use () =
  let first = First.launch () in
  let second = Second.launch () in
  let y = Second.finish second in
  let x = First.finish first in
  x + y
(*@ result = use () ensures result === 2 *)

let direct () =
  let domain = Domain.spawn First.work in
  Domain.join domain
(*@ result = direct () ensures result === 1 *)

let returned () =
  let domain = First.launch () in
  Domain.join domain
(*@ result = returned () ensures result === 1 *)
