type 'a t = 'a Atomic.t

let create value = Atomic.make value
(*@ initially { value = value } *)

let integer () = create 17
let boolean () = create true
