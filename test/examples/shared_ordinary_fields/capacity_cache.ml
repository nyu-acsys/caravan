type cache = { mutable capacity : int [@caravan.relaxed] }

let create (limit : int) (tail : int) (initial_head : int) =
  let head = Atomic.make initial_head in
  let cache = { capacity = 0 } in
  (head, cache)

let read (head : int Atomic.t) cache (limit : int) (tail : int) = cache.capacity

let refresh head cache limit tail =
  let observed_head = Atomic.get head in
  let available = limit - (tail - observed_head) in
  cache.capacity <- available

let advance head (cache : cache) (limit : int) tail =
  let previous = Atomic.get head in
  if previous < tail then Atomic.compare_and_set head previous (previous + 1) else false

let next_capacity head cache limit tail =
  let capacity = read head cache limit tail in
  if capacity > 0 then Some (capacity - 1) else None

let exercise () =
  let head, cache = create 4 8 4 in
  let _ = advance head cache 4 8 in
  refresh head cache 4 8;
  next_capacity head cache 4 8

let stale_positive () =
  let cache = { capacity = 1 } in
  cache.capacity <- 3;
  let capacity = cache.capacity in
  capacity - 1

let zero_refresh () =
  let cache = { capacity = 0 } in
  cache.capacity <- 3;
  let capacity = cache.capacity in
  if capacity = 0 then 4 - (8 - 7) else capacity

let published_create (limit : int) (tail : int) (initial_head : int) =
  let head = Atomic.make initial_head in
  let cache = { capacity = -1 } in
  cache.capacity <- 0;
  (head, cache)

let published_read (head : int Atomic.t) cache (limit : int) (tail : int) = cache.capacity

let published_refresh head cache limit tail =
  let observed_head = Atomic.get head in
  let available = limit - (tail - observed_head) in
  cache.capacity <- available

let published_advance head (cache : cache) (limit : int) tail =
  let previous = Atomic.get head in
  if previous < tail then Atomic.compare_and_set head previous (previous + 1) else false

let published_next_capacity head cache limit tail =
  let capacity = published_read head cache limit tail in
  if capacity > 0 then Some (capacity - 1) else None

let published_exercise () =
  let head, cache = published_create 4 8 4 in
  let _ = published_advance head cache 4 8 in
  published_refresh head cache 4 8;
  published_next_capacity head cache 4 8
