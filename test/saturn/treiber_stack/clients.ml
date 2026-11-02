let integer_client () =
  let stack = create () in
  push stack 17;
  push stack 23;
  let first = pop_opt stack in
  let rest = pop_all stack in
  assert (first = Some 23);
  assert (rest = [ 17 ]);
  assert (is_empty stack)

let boolean_client () =
  let stack = of_list [ true; false ] in
  let first = pop_opt stack in
  push stack true;
  let rest = pop_all stack in
  assert (first = Some true);
  assert (rest = [ true; false ]);
  assert (is_empty stack)
