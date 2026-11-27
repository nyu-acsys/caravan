let identity value = value

let selected ?(value = 7) () =
  let selected = identity (value + 1) in
  selected

let pattern ?(value = 7) (first, second) =
  let selected = identity (value + first) in
  selected - second

let clients () = (selected (), selected ~value:9 (), pattern (2, 1))
