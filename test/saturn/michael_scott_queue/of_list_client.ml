let empty () =
  let q : int Michael_scott_queue.t = Michael_scott_queue.of_list [] in
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

let integers () =
  let q = Michael_scott_queue.of_list [ 1; 2 ] in
  assert (Michael_scott_queue.pop_opt q = Some 1);
  Michael_scott_queue.push q 3;
  assert (Michael_scott_queue.pop_opt q = Some 2);
  assert (Michael_scott_queue.pop_opt q = Some 3);
  assert (Michael_scott_queue.is_empty q)

let mixed () =
  let ints = Michael_scott_queue.create () in
  let bools = Michael_scott_queue.of_list [ true ] in
  Michael_scott_queue.push ints 7;
  assert (Michael_scott_queue.pop_opt bools = Some true);
  assert (Michael_scott_queue.pop_opt ints = Some 7);
  assert (Michael_scott_queue.is_empty ints);
  assert (Michael_scott_queue.is_empty bools)

let roundtrip value =
  let q = Michael_scott_queue.of_list [ value ] in
  match Michael_scott_queue.pop_opt q with Some result -> result | None -> assert false
(*@ result = roundtrip value
    ensures result === value *)

let mutable_payload () =
  let value = ref 7 in
  let q = Michael_scott_queue.of_list [ value ] in
  match Michael_scott_queue.pop_opt q with
  | None -> assert false
  | Some result ->
      assert (result == value);
      assert (!result = 7)
