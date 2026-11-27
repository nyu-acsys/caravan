let initialize_node value =
  let node = make_node ~value ~capacity:0 ~counter:0 Null in
  set_counter node 7;
  set_capacity node 3;
  get_counter node

let stale_capacity value =
  let node = make_node ~value ~capacity:0 ~counter:0 Null in
  set_capacity node 3;
  let first = get_capacity node in
  set_capacity node 2;
  let second = get_capacity node in
  (first, second)

let link_candidate value =
  let first = make_node ~value ~capacity:1 ~counter:0 Null in
  let second : (_, [ `Node ]) node = make_node ~value ~capacity:0 ~counter:1 Null in
  let linked = compare_and_set_next first (Link Null) (Link second) in
  if linked then begin
    let actual = link_as_node (fenceless_get_next first) in
    let counter = get_counter actual in
    Some (counter, actual, second)
  end
  else begin
    set_counter second 2;
    None
  end

let failed_retry value =
  let successor = make_node ~value ~capacity:0 ~counter:1 Null in
  let first = make_node ~value ~capacity:1 ~counter:0 successor in
  let candidate : (_, [ `Node ]) node = make_node ~value ~capacity:0 ~counter:1 Null in
  let linked = compare_and_set_next first (Link Null) (Link candidate) in
  set_counter candidate 2;
  (linked, candidate)

let help_current_tail queue =
  let node = Atomic.get queue.tail in
  fix_tail queue.tail node

let push_once value =
  let queue = create ~capacity:2 () in
  let pushed = try_push queue value in
  (queue, pushed)

let push_or_raise value =
  let queue = create ~capacity:2 () in
  push_exn queue value;
  queue

let peek_empty () : bool option =
  let queue = create ~capacity:2 () in
  peek_opt queue

let peek_empty_exn () : bool =
  let queue = create ~capacity:2 () in
  peek_exn queue

let push_peek value =
  let queue = create ~capacity:2 () in
  let pushed = try_push queue value in
  let observed = peek_opt queue in
  (pushed, observed)

let push_peek_exn value =
  let queue = create ~capacity:2 () in
  push_exn queue value;
  peek_exn queue

let pop_empty () : bool option =
  let queue = create ~capacity:2 () in
  pop_opt queue

let pop_empty_exn () : bool =
  let queue = create ~capacity:2 () in
  pop_exn queue

let push_pop value =
  let queue = create ~capacity:2 () in
  let pushed = try_push queue value in
  let observed = pop_opt queue in
  (pushed, observed)

let push_pop_exn value =
  let queue = create ~capacity:2 () in
  push_exn queue value;
  pop_exn queue

let fifo_reuse first second =
  let queue = create ~capacity:2 () in
  push_exn queue first;
  push_exn queue second;
  let removed = pop_exn queue in
  let observed = peek_exn queue in
  drop_exn queue;
  let again = first in
  push_exn queue again;
  let reused = pop_exn queue in
  let empty = pop_opt queue in
  (removed, observed, reused, empty)

let empty_query () =
  let queue : bool t = create ~capacity:1 () in
  is_empty queue

let query_cycle value =
  let queue = create ~capacity:1 () in
  let before = is_empty queue in
  push_exn queue value;
  let during = is_empty queue in
  let removed = pop_exn queue in
  let after = is_empty queue in
  (before, during, after, removed)

let fullness_cycle value =
  let queue = create ~capacity:1 () in
  let before = is_full queue in
  push_exn queue value;
  let during = is_full queue in
  let count = length queue in
  let removed = pop_exn queue in
  let after = is_full queue in
  (before, during, count, after, removed)

let zero_capacity_full () =
  let queue : bool t = create ~capacity:0 () in
  is_full queue

module Push_contract_clients = struct
  let push_available value =
    let queue = create ~capacity:1 () in
    let accepted = try_push queue value in
    let observed = peek_opt queue in
    (accepted, observed)

  let push_full value =
    let queue = create ~capacity:1 () in
    push_exn queue value;
    try_push queue value

  let push_exn_zero value =
    let queue = create ~capacity:0 () in
    push_exn queue value

  let push_reuse value =
    let queue = create ~capacity:1 () in
    let first = try_push queue value in
    let removed = pop_opt queue in
    let second = try_push queue value in
    (first, removed, second)
end
