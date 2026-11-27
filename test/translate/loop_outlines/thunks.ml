let work value = value

let run () =
  let first = Domain.spawn (fun () -> work 1) in
  let second = Domain.spawn (fun () -> work 2) in
  let left = Domain.join first in
  let right = Domain.join second in
  left + right
