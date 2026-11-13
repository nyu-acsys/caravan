let identity value = value

let outer () =
  let choose ?(value = identity 42) () = identity value in
  choose ()
