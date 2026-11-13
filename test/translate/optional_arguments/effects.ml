let bump cell =
  cell := !cell + 1;
  !cell

let choose cell ?(value = bump cell) () = value

let local cell ?(value = bump cell) () =
  let keep () = value in
  keep ()

let touch cell ?(token = cell := !cell + 1) () = token

let client () =
  let cell = ref 0 in
  assert (choose cell ~value:7 () = 7);
  assert (!cell = 0);
  assert (choose cell () = 1);
  assert (!cell = 1);
  assert (local cell ~value:9 () = 9);
  assert (!cell = 1);
  assert (local cell () = 2);
  assert (!cell = 2);
  touch cell ~token:() ();
  assert (!cell = 2);
  touch cell ();
  assert (!cell = 3)

let unowned cell = choose cell ~value:7 ()
