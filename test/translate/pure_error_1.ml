let check (x : int) =
  assert (x > 0);
  x

let f (x : int) = x
(*@ r = f x
    ensures r = check x *)
