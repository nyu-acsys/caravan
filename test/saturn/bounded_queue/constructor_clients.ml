module Constructor_clients = struct
  let full_at_one value =
    let queue = of_list_exn ~capacity:1 [ value ] in
    try_push queue value

  let fifo_two first second =
    let queue = of_list_exn ~capacity:2 [ first; second ] in
    let removed = pop_exn queue in
    let next = pop_exn queue in
    let empty = pop_opt queue in
    (removed, next, empty)

  let empty_zero () =
    let queue : int t = of_list_exn ~capacity:0 [] in
    let empty = is_empty queue in
    let full = is_full queue in
    (empty, full)

  let spare_reuse first second =
    let queue = of_list_exn ~capacity:2 [ first ] in
    let accepted = try_push queue second in
    let removed = pop_exn queue in
    push_exn queue first;
    let next = pop_exn queue in
    (accepted, removed, next)

  let oversized first second = of_list_exn ~capacity:1 [ first; second ]

  let default_capacity first second =
    let queue = of_list_exn [ first; second ] in
    capacity_of queue
end
