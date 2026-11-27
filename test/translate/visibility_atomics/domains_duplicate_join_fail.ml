type unused = { mutable frozen : int [@caravan.frozen] }

let read (channel : int Atomic.t) = Atomic.get channel
(*@ result = read channel requires own channel value
    ensures own channel value && result === value *)

let bad channel =
  let child = Domain.spawn (fun () -> read channel) in
  let _ = Domain.join child in
  Domain.join child
(*@ result = bad channel requires own channel value
    ensures own channel value && result === value *)
