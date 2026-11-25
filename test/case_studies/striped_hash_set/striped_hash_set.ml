(* A lock-striped hash set, following Herlihy and Shavit's
   "The Art of Multiprocessor Programming", Section 13.2.2. Each stripe owns a row
   of buckets; resizing holds all stripes while replacing the table. *)

type t = {
  locks : Mutex.t array;
  table : int list array array Atomic.t;
  size : int Atomic.t;
}

let rec mem (x : int) bucket =
  match bucket with [] -> false | y :: rest -> y = x || mem x rest

let rec without (x : int) bucket =
  match bucket with
  | [] -> []
  | y :: rest -> if y = x then without x rest else y :: without x rest

let create stripes =
  let rows = Array.make stripes (Array.make 1 []) in
  let table = Atomic.make rows in
  let locks = Array.make stripes (Mutex.create ()) in
  for i = 0 to stripes - 1 do
    rows.(i) <- Array.make 1 [];
    locks.(i) <- Mutex.create ()
  done;
  { locks; table; size = Atomic.make 0 }

let[@inline] stripe_count s = Array.length s.locks
let[@inline] bucket_index x stripes capacity = x / stripes mod capacity

let contains s x =
  let stripes = stripe_count s in
  let stripe = x mod stripes in
  let lock = s.locks.(stripe) in
  Mutex.lock lock;
  let row = (Atomic.get s.table).(stripe) in
  let result = mem x row.(bucket_index x stripes (Array.length row)) in
  Mutex.unlock lock;
  result

let add s x =
  let stripes = stripe_count s in
  let stripe = x mod stripes in
  let lock = s.locks.(stripe) in
  Mutex.lock lock;
  let row = (Atomic.get s.table).(stripe) in
  let bucket = bucket_index x stripes (Array.length row) in
  let added = not (mem x row.(bucket)) in
  if added then row.(bucket) <- x :: row.(bucket);
  Mutex.unlock lock;
  if added then Atomic.incr s.size;
  added

let remove s x =
  let stripes = stripe_count s in
  let stripe = x mod stripes in
  let lock = s.locks.(stripe) in
  Mutex.lock lock;
  let row = (Atomic.get s.table).(stripe) in
  let bucket = bucket_index x stripes (Array.length row) in
  let removed = mem x row.(bucket) in
  if removed then row.(bucket) <- without x row.(bucket);
  Mutex.unlock lock;
  if removed then Atomic.decr s.size;
  removed

let rec rehash row capacity stripes bucket =
  match bucket with
  | [] -> ()
  | x :: rest ->
      let target = bucket_index x stripes capacity in
      row.(target) <- x :: row.(target);
      rehash row capacity stripes rest

let empty_row capacity = Array.make capacity []

let rebuild old_row capacity stripes =
  let row = empty_row capacity in
  for k = 0 to Array.length old_row - 1 do
    rehash row capacity stripes old_row.(k)
  done;
  row

let resize_locked s old_capacity =
  let stripes = stripe_count s in
  let old_table = Atomic.get s.table in
  let growing =
    Array.length old_table.(0) = old_capacity && old_capacity <= 9007199254740991
  in
  if growing then begin
    let capacity = 2 * old_capacity in
    let table = Array.make stripes (Array.make 1 []) in
    for i = 0 to stripes - 1 do
      let row = rebuild old_table.(i) capacity stripes in
      table.(i) <- row
    done;
    Atomic.set s.table table
  end

let resize s old_capacity =
  let stripes = stripe_count s in
  for i = 0 to stripes - 1 do
    Mutex.lock s.locks.(i)
  done;
  resize_locked s old_capacity;
  for i = 0 to stripes - 1 do
    Mutex.unlock s.locks.(i)
  done
