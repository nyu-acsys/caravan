let independent () =
  let first = First.of_list [ 1; 2 ] in
  let second = Second.of_list [ 7 ] in
  Alias.push first 3;
  Second.push second 8;
  assert (Alias.pop_opt first = Some 1);
  assert (Second.pop_opt second = Some 7);
  assert (First.pop_opt first = Some 2);
  assert (Second.pop_opt second = Some 8);
  assert (Alias.pop_opt first = Some 3);
  assert (First.is_empty first);
  assert (Second.is_empty second)
