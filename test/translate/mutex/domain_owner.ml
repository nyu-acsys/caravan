let work () = ()

let client () =
  let child = Domain.spawn work in
  Domain.join child
