let empty () =
  let q = Alias.create () in
  assert (Alias.is_empty q);
  assert (Alias.pop_opt q = None)

let singleton () =
  let q = Alias.of_list [ 7 ] in
  assert (not (Alias.is_empty q));
  assert (Alias.pop_opt q = Some 7);
  assert (Alias.is_empty q)

let longer () =
  let q = Alias.of_list [ 1; 2; 3 ] in
  assert (Alias.pop_opt q = Some 1);
  Alias.push q 4;
  assert (Alias.pop_opt q = Some 2);
  assert (Alias.pop_opt q = Some 3);
  assert (Alias.pop_opt q = Some 4);
  assert (Alias.pop_opt q = None);
  assert (Alias.is_empty q)

let empty_of_list () =
  let q = Alias.of_list [] in
  assert (Alias.is_empty q);
  assert (Alias.pop_opt q = None)
