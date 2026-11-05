type t = { anchor : int Atomic.t; contents : int Atomic.t }

let make value =
  let build (value : int) = Atomic.make value in
  let contents = build value in
  let anchor = Atomic.make 0 in
  { anchor; contents }
(*@ initially { value = value } *)
