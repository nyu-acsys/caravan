type 'a t = { cell : 'a Atomic.t }

let create value = { cell = Atomic.make value }
(*@ initially { value = value } *)

let read q = Atomic.get q.cell (*@ commit *)

let integer () =
  let q = create 17 in
  read q
(*@ result = integer () ensures result === 17 *)

let boolean () =
  let q = create true in
  read q
(*@ result = boolean () ensures result *)
