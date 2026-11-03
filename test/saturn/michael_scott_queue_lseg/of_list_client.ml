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

let booleans () =
  let q = Michael_scott_queue_lseg.of_list [ true; false ] in
  assert (Michael_scott_queue_lseg.pop_opt q = Some true);
  Michael_scott_queue_lseg.push q true;
  assert (Michael_scott_queue_lseg.pop_opt q = Some false);
  assert (Michael_scott_queue_lseg.pop_opt q = Some true);
  assert (Michael_scott_queue_lseg.pop_opt q = None);
  assert (Michael_scott_queue_lseg.is_empty q)

let independent_instances () =
  let integers = Michael_scott_queue_lseg.create () in
  let booleans = Michael_scott_queue_lseg.create () in
  Michael_scott_queue_lseg.push integers 17;
  Michael_scott_queue_lseg.push booleans true;
  assert (Michael_scott_queue_lseg.pop_opt integers = Some 17);
  assert (Michael_scott_queue_lseg.pop_opt booleans = Some true)

let mutable_payload () =
  let value = ref 7 in
  let q = Michael_scott_queue_lseg.of_list [ value ] in
  match Michael_scott_queue_lseg.pop_opt q with
  | None -> assert false
  | Some result ->
      assert (result == value);
      assert (!result = 7)
