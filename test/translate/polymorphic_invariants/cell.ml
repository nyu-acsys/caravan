type 'a t = 'a Atomic.t

let create value = Atomic.make value
(*@ initially { value = value } *)

let read (q : 'a t) = Atomic.get q (*@ commit *)

let rec set q value =
  let before = Atomic.get q in
  if Atomic.compare_and_set q before value (*@ performs replace *) then ()
  else set q value

let rec set_left (left : int t) (right : bool t) value =
  let before = Atomic.get left in
  if Atomic.compare_and_set left before value (*@ performs replace *) then ()
  else set_left left right value

let mixed () =
  let left = create 17 in
  let right = create false in
  set_left left right 42;
  (read left, read right)

let integer () =
  let q = create 17 in
  set q 42;
  read q
(*@ result = integer () ensures result === 42 *)

let boolean () =
  let q = create false in
  set q true;
  read q
(*@ result = boolean () ensures result *)
