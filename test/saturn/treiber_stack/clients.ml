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

let exception_client () =
  let stack = create () in
  push stack 5;
  push stack 7;
  let top = peek_exn stack in
  let popped = pop_exn stack in
  drop_exn stack;
  assert (top = 7 && popped = 7);
  assert (peek_opt stack = None);
  match pop_exn stack with _ -> assert false | exception Empty -> ()

let bulk_empty_client () =
  let stack = of_list [ 17; 23 ] in
  push_all stack [];
  assert (pop_all stack = [ 17; 23 ])

let bulk_order_client () =
  let stack = create () in
  push_all stack [ 1; 2; 3 ];
  assert (pop_opt stack = Some 3);
  assert (pop_all stack = [ 2; 1 ])

let bulk_existing_client () =
  let stack = of_list [ 9; 8 ] in
  push_all stack [ 1; 2 ];
  push_all stack [ 3 ];
  assert (pop_all stack = [ 3; 2; 1; 9; 8 ])

let bulk_boolean_client () =
  let stack = of_list [ false ] in
  push_all stack [ true; false ];
  assert (pop_all stack = [ false; true; false ])
