let empty () =
  let q = Michael_scott_queue.of_list [] in
  assert (Michael_scott_queue.is_empty q);
  assert (Michael_scott_queue.pop_opt q = None)

let singleton () =
  let q = Michael_scott_queue.of_list [ 7 ] in
  assert (not (Michael_scott_queue.is_empty q));
  assert (Michael_scott_queue.pop_opt q = Some 7);
  assert (Michael_scott_queue.is_empty q)

let longer () =
  let q = Michael_scott_queue.of_list [ 1; 2; 3 ] in
  assert (Michael_scott_queue.pop_opt q = Some 1);
  Michael_scott_queue.push q 4;
  assert (Michael_scott_queue.pop_opt q = Some 2);
  assert (Michael_scott_queue.pop_opt q = Some 3);
  assert (Michael_scott_queue.pop_opt q = Some 4);
  assert (Michael_scott_queue.pop_opt q = None);
  assert (Michael_scott_queue.is_empty q)
