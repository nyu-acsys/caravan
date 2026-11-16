let target_bool queue value = if try_push queue value then "pushed" else "full"

let target_unit queue value =
  try
    push_exn queue value;
    "pushed"
  with Full -> "full"

let run_wrapped label target_push value =
  let queue = create ~capacity:2 () in
  push_exn queue 10;
  push_exn queue 11;
  ignore (pop_exn queue);
  ignore (pop_exn queue);
  assert (length queue = 0);
  assert (get_capacity (Atomic.get queue.tail) = 0);
  Atomic.set target_paused false;
  Atomic.set release_target false;
  Atomic.set pause_armed true;
  let target = Domain.spawn (fun () -> target_push queue value) in
  while not (Atomic.get target_paused) do
    Domain.cpu_relax ()
  done;
  (* Signed 3-bit max_small_int is 3; run max_small_int - 1 = 2 pairs. *)
  for i = 0 to 1 do
    push_exn queue (20 + i);
    ignore (pop_exn queue)
  done;
  let head_counter = get_counter (Atomic.get queue.head) in
  let tail_counter = get_counter (Atomic.get queue.tail) in
  assert (head_counter = -4 && tail_counter = -4);
  Atomic.set release_target true;
  let outcome = Domain.join target in
  let queued_target = peek_opt queue = Some value in
  Printf.printf "%s: target=%s; queued_target=%b\n" label outcome queued_target;
  (outcome, queued_target)

let full_checks () =
  let queue = create ~capacity:2 () in
  push_exn queue 1;
  push_exn queue 2;
  let bool_result = try_push queue 3 in
  let unit_full =
    try
      push_exn queue 3;
      false
    with Full -> true
  in
  assert ((not bool_result) && unit_full);
  let zero = create ~capacity:0 () in
  let zero_bool = try_push zero 4 in
  let zero_unit_full =
    try
      push_exn zero 4;
      false
    with Full -> true
  in
  assert ((not zero_bool) && zero_unit_full);
  Printf.printf "genuine full capacity=2: Bool=false; Unit=Full\n";
  Printf.printf "capacity=0: Bool=false; Unit=Full\n"

let of_list_checks () =
  let full_bool = of_list_exn ~capacity:1 [ 7 ] in
  let full_unit = of_list_exn ~capacity:1 [ 7 ] in
  let rejected_bool = not (try_push full_bool 8) in
  let rejected_unit =
    try
      push_exn full_unit 8;
      false
    with Full -> true
  in
  assert (is_full full_bool && is_full full_unit);
  assert (rejected_bool && rejected_unit);
  let fifo = of_list_exn ~capacity:4 [ 1; 2; 3 ] in
  assert (length fifo = 3 && not (is_full fifo));
  push_exn fifo 4;
  assert (List.init 4 (fun _ -> pop_exn fifo) = [ 1; 2; 3; 4 ]);
  assert (is_empty fifo && length fifo = 0 && peek_opt fifo = None);
  let empty = of_list_exn ~capacity:2 [] in
  assert (is_empty empty && length empty = 0 && not (is_full empty));
  let zero = of_list_exn ~capacity:0 [] in
  assert (is_empty zero && is_full zero);
  let zero_rejected =
    try
      ignore (of_list_exn ~capacity:0 [ 1 ]);
      false
    with Full -> true
  in
  let oversize =
    try
      ignore (of_list_exn ~capacity:1 [ 1; 2 ]);
      false
    with Full -> true
  in
  assert (zero_rejected && oversize);
  Printf.printf
    "of_list_exn: capacity=1 full/rejected; FIFO=ok; empty=ok; spare capacity=ok; \
     oversize=Full; capacity=0=Full\n"

let constructor_original_probe () =
  let bool_queue = of_list_exn ~capacity:1 [ 7 ] in
  let unit_queue = of_list_exn ~capacity:1 [ 7 ] in
  let bool_result = try_push bool_queue 8 in
  let unit_result =
    try
      push_exn unit_queue 8;
      "pushed"
    with Full -> "full"
  in
  Printf.printf "capacity=1 old cache initializers: Bool=%b; Unit=%s; lengths=%d/%d\n"
    bool_result unit_result (length bool_queue) (length unit_queue)

let () =
  if Array.length Sys.argv > 1 && String.equal Sys.argv.(1) "constructor-original" then
    constructor_original_probe ()
  else begin
    let bool_outcome, bool_item = run_wrapped "Bool wrapper" target_bool 99 in
    let unit_outcome, unit_item = run_wrapped "Unit wrapper" target_unit 98 in
    full_checks ();
    of_list_checks ();
    Printf.printf "summary: Bool=%s/%b; Unit=%s/%b; model=signed 3-bit [-4,3]\n"
      bool_outcome bool_item unit_outcome unit_item
  end
