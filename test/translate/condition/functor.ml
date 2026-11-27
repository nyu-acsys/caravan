module type Element = sig
  type t
end

module Worker (A : Element) = struct
  let create (value : A.t) =
    let mutex = Mutex.create () in
    let condition = Condition.create () in
    (mutex, condition)

  let work mutex condition (value : A.t) =
    Mutex.lock mutex;
    Condition.wait condition mutex;
    Mutex.unlock mutex;
    value

  let launch mutex condition value = Domain.spawn (fun () -> work mutex condition value)

  let finish (domain : A.t Domain.t) (mutex : Mutex.t) (condition : Condition.t)
      (value : A.t) =
    Domain.join domain
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
  let first_mutex, first_condition = First.create 7 in
  let second_mutex, second_condition = Second.create true in
  let first = First.launch first_mutex first_condition 7 in
  let second = Second.launch second_mutex second_condition true in
  let flag = Second.finish second second_mutex second_condition true in
  let number = Again.finish first first_mutex first_condition 7 in
  assert flag;
  number + 1
