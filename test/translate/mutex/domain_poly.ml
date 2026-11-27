let work (mutex : Mutex.t) value =
  Mutex.lock mutex;
  Mutex.unlock mutex;
  value

let launch mutex value = Domain.spawn (fun () -> work mutex value)
let finish (domain : 'a Domain.t) (mutex : Mutex.t) (value : 'a) = Domain.join domain

let client () =
  let mutex = Mutex.create () in
  let first = launch mutex 7 in
  let second = launch mutex true in
  let flag = finish second mutex true in
  let number = finish first mutex 7 in
  assert flag;
  number + 1
