type 'a t = 'a Atomic.t

let create value = Atomic.make value
(*@ initially { value = value } *)

let read q = Atomic.get q (*@ commit *)

let set q value =
  let rec helper target item =
    let before = Atomic.get target in
    if Atomic.compare_and_set target before item then () else helper target item
    (*@ helper target item
        continues set
        requires target == q && item === value *)
  in
  helper q value

let set_right (left : 'a t) right value =
  let rec helper target item =
    let before = Atomic.get target in
    if Atomic.compare_and_set target before item then () else helper target item
    (*@ helper target item
        continues set_right
        requires target == right && item === value *)
  in
  helper right value

let mixed () =
  let ints = create 17 in
  let bools = create false in
  set ints 23;
  set bools true;
  set_right ints bools false;
  (read ints, read bools)
