let keep r s =
  r := 1;
  s := 2;
  (*@ cut own r.contents 1 *)
  r := 3;
  !r

let read_restated r =
  let x = !r in
  (*@ cut own r.contents x && x = a *)
  r := 3;
  x
