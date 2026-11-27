let client () =
  assert (Optional.choose 42 () = 42);
  assert (Optional.choose true ~value:false () = false)
