type t = int Atomic.t

let create () = Atomic.make 0
(*@ initially { value = 0 } *)

let rec set_one c =
  if Atomic.compare_and_set c 0 1 (*@ performs set_one *) then () else set_one c

let read (c : t) = Atomic.get c (*@ commit *)

let exercise () =
  let c = create () in
  set_one c;
  read c
