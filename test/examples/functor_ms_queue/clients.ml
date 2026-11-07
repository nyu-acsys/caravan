let independent () =
  let first = First.of_list [ true; false ] in
  let second = Second.of_list [ false ] in
  Alias.push first true;
  Second.push second true;
  assert (Alias.pop_opt first = Some true);
  assert (Second.pop_opt second = Some false);
  assert (First.pop_opt first = Some false);
  assert (Second.pop_opt second = Some true);
  assert (Alias.pop_opt first = Some true);
  assert (First.is_empty first);
  assert (Second.is_empty second)
