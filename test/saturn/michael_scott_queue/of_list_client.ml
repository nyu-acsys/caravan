let empty () =
  let q = Michael_scott_queue.of_list [] in
  assert (Michael_scott_queue.is_empty q);
  assert (Michael_scott_queue.pop_opt q = None)

let singleton () =
  let q = Michael_scott_queue.of_list [ true ] in
  assert (not (Michael_scott_queue.is_empty q));
  assert (Michael_scott_queue.pop_opt q = Some true);
  assert (Michael_scott_queue.is_empty q)

let longer () =
  let q = Michael_scott_queue.of_list [ true; false; false ] in
  assert (Michael_scott_queue.pop_opt q = Some true);
  Michael_scott_queue.push q true;
  assert (Michael_scott_queue.pop_opt q = Some false);
  assert (Michael_scott_queue.pop_opt q = Some false);
  assert (Michael_scott_queue.pop_opt q = Some true);
  assert (Michael_scott_queue.pop_opt q = None);
  assert (Michael_scott_queue.is_empty q)
