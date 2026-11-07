type 'a t = 'a Atomic.t

let create value = Atomic.make value
(*@ initially { value = value; tag = max_int + 1 } *)

let read (q : 'a t) = Atomic.get q (*@ commit *)

let integer () =
  let q = create 17 in
  read q
(*@ result = integer () ensures result === 17 *)

let boolean () =
  let q = create true in
  read q
(*@ result = boolean () ensures result *)
