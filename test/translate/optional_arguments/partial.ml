let choose ?(value = 42) () = value

let client () =
  let pending = choose ~value:1 in
  pending ()
