let make (cell : int ref) =
  let mutex = Mutex.create () in
  let condition = Condition.create () in
  (mutex, condition)

let await mutex condition =
  Mutex.lock mutex;
  Condition.wait condition mutex;
  Mutex.unlock mutex

let signal condition = Condition.signal condition
let broadcast condition = Condition.broadcast condition

let refresh mutex condition (cell : int ref) =
  Mutex.lock mutex;
  let before = !cell in
  Condition.wait condition mutex;
  let after = !cell in
  Mutex.unlock mutex;
  after

let client () =
  let cell = ref 0 in
  let mutex, condition = make cell in
  signal condition;
  broadcast condition;
  await mutex condition;
  refresh mutex condition cell
