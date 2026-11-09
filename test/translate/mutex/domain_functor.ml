module type Element = sig
  type t
end

module Worker (A : Element) = struct
  let create (value : A.t) = Mutex.create ()

  let work (mutex : Mutex.t) (value : A.t) =
    Mutex.lock mutex;
    Mutex.unlock mutex;
    value

  let launch mutex value = Domain.spawn (fun () -> work mutex value)
  let finish (domain : A.t Domain.t) (mutex : Mutex.t) (value : A.t) = Domain.join domain
end

module Int = struct
  type t = int
end

module Bool = struct
  type t = bool
end

module First = Worker (Int)
module Again = Worker (Int)
module Second = Worker (Bool)

let client () =
  let first_mutex = First.create 7 in
  let second_mutex = Second.create true in
  let first = First.launch first_mutex 7 in
  let second = Second.launch second_mutex true in
  let flag = Second.finish second second_mutex true in
  let number = Again.finish first first_mutex 7 in
  assert flag;
  number + 1
