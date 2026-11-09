type ('a, 'b) t = {
  mutable value : 'a;
  mutable other : 'b;
  mutex : Mutex.t;
  condition : Condition.t;
}

let create value other =
  { value; other; mutex = Mutex.create (); condition = Condition.create () }

let await (cell : ('a, 'b) t) =
  Mutex.lock cell.mutex;
  Condition.wait cell.condition cell.mutex;
  Mutex.unlock cell.mutex

let client () =
  let first = create 17 false in
  let second = create true 42 in
  await first;
  await second
