type 'a t = 'a list Atomic.t

let create (value : 'a list) : 'a t = Atomic.make value
(*@ initially { value = value } *)

let read (q : 'a t) : 'a list = Atomic.get q (*@ commit *)
