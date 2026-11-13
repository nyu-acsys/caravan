let client () =
  assert (Labelled.keep ~tag:0 ~value:42 = 42);
  assert (Labelled.keep ~value:true ~tag:1)
