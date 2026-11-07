let empty () =
  let q : bool Alias.t = Alias.create () in
  assert (Alias.is_empty q);
  assert (Alias.pop_opt q = None)

let singleton () =
  let q = Alias.of_list [ true ] in
  assert (not (Alias.is_empty q));
  assert (Alias.pop_opt q = Some true);
  assert (Alias.is_empty q)

let longer () =
  let q = Alias.of_list [ true; false; false ] in
  assert (Alias.pop_opt q = Some true);
  Alias.push q true;
  assert (Alias.pop_opt q = Some false);
  assert (Alias.pop_opt q = Some false);
  assert (Alias.pop_opt q = Some true);
  assert (Alias.pop_opt q = None);
  assert (Alias.is_empty q)

let empty_of_list () =
  let q : bool Alias.t = Alias.of_list [] in
  assert (Alias.is_empty q);
  assert (Alias.pop_opt q = None)
