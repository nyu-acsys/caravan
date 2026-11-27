let successor counter = counter + 1

let refresh limit tail_counter head_counter =
  let length = tail_counter - head_counter in
  limit - length

let decrement capacity = capacity - 1

let crossing () =
  let tail = successor max_int in
  let head = max_int in
  refresh 4 tail head

let stale_tail_full () =
  let tail = max_int in
  let head = successor tail in
  refresh max_int tail head <= 0

type cache = { mutable capacity : int [@caravan.relaxed] }

let make_cache capacity = { capacity }
let read_cache cache = cache.capacity

let refresh_cache cache limit tail_counter head_counter =
  let length = tail_counter - head_counter in
  let available = limit - length in
  if 0 < available then cache.capacity <- available

let successor_cache cache =
  let capacity = cache.capacity in
  if 0 < capacity then Some { capacity = capacity - 1 } else None

let moving_tail () =
  let counter = successor max_int in
  let cache = make_cache 1 in
  match successor_cache cache with
  | None -> None
  | Some next ->
      refresh_cache cache 4 max_int counter;
      let old_capacity = read_cache cache in
      let new_capacity = read_cache next in
      Some (old_capacity, new_capacity)
