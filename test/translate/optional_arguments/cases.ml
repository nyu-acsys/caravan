let identity value = value
let choose ?(value = identity 42) = function () -> identity value

let client () =
  assert (choose () = 42);
  assert (choose ~value:7 () = 7)
