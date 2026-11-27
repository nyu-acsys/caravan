type 'a t = { mutable value : 'a; mutex : Mutex.t; condition : Condition.t }

let create value = { value; mutex = Mutex.create (); condition = Condition.create () }

let await (cell : 'a t) =
  Mutex.lock cell.mutex;
  Condition.wait cell.condition cell.mutex;
  Mutex.unlock cell.mutex

let client () =
  let first = create 17 in
  let second = create true in
  await first;
  await second
