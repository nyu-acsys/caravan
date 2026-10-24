let empty () =
  let q = Michael_scott_queue_lseg.of_list [] in
  assert (Michael_scott_queue_lseg.is_empty q);
  assert (Michael_scott_queue_lseg.pop_opt q = None);
  Michael_scott_queue_lseg.push q 7;
  assert (Michael_scott_queue_lseg.pop_opt q = Some 7);
  assert (Michael_scott_queue_lseg.is_empty q)

let singleton () =
  let q = Michael_scott_queue_lseg.of_list [ 1 ] in
  assert (not (Michael_scott_queue_lseg.is_empty q));
  Michael_scott_queue_lseg.push q 2;
  assert (Michael_scott_queue_lseg.pop_opt q = Some 1);
  assert (Michael_scott_queue_lseg.pop_opt q = Some 2);
  assert (Michael_scott_queue_lseg.pop_opt q = None)

let longer () =
  let q = Michael_scott_queue_lseg.of_list [ 1; 2; 3 ] in
  assert (Michael_scott_queue_lseg.pop_opt q = Some 1);
  Michael_scott_queue_lseg.push q 4;
  assert (Michael_scott_queue_lseg.pop_opt q = Some 2);
  assert (Michael_scott_queue_lseg.pop_opt q = Some 3);
  assert (Michael_scott_queue_lseg.pop_opt q = Some 4);
  assert (Michael_scott_queue_lseg.is_empty q)
