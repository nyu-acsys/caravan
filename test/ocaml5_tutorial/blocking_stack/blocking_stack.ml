module Atomic_stack : sig
  type 'a t
  val make : unit -> 'a t
  val push : 'a t -> 'a -> unit
  val pop  : 'a t -> 'a
end = struct
  type 'a t = {
    mutable contents: 'a list;
    mutex : Mutex.t;
    condition : Condition.t
  }

  let make () = {
    contents = [];
    mutex = Mutex.create ();
    condition = Condition.create ()
  }

  let push r v =
    Mutex.lock r.mutex;
    r.contents <- v::r.contents;
    Condition.signal r.condition;
    Mutex.unlock r.mutex

  let pop r =
    Mutex.lock r.mutex;
    let rec loop () =
      match r.contents with
      | [] ->
          Condition.wait r.condition r.mutex;
          loop ()
      | x::xs -> r.contents <- xs; x
    in
    let res = loop () in
    Mutex.unlock r.mutex;
    res
end

let integer_lifo () =
  let stack = Atomic_stack.make () in
  Atomic_stack.push stack 17;
  Atomic_stack.push stack 42;
  let top = Atomic_stack.pop stack in
  let next = Atomic_stack.pop stack in
  (top, next)

let boolean_lifo () =
  let stack = Atomic_stack.make () in
  Atomic_stack.push stack true;
  Atomic_stack.push stack false;
  let top = Atomic_stack.pop stack in
  let next = Atomic_stack.pop stack in
  (top, next)

let produce stack =
  Atomic_stack.push stack 17;
  Atomic_stack.push stack 42

let handoff () =
  let stack = Atomic_stack.make () in
  let producer = Domain.spawn (fun () -> produce stack) in
  Domain.join producer;
  let top = Atomic_stack.pop stack in
  let next = Atomic_stack.pop stack in
  (top, next)
