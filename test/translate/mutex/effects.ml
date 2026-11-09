exception Acquired of int
exception Unchanged of int
exception Released
exception Retained

let acquire (mutex : Mutex.t) (cell : int ref) = Mutex.lock mutex
let release (mutex : Mutex.t) (cell : int ref) = Mutex.unlock mutex

let acquire_or_raise (mutex : Mutex.t) (cell : int ref) choice =
  if choice = 0 then raise (Unchanged choice);
  acquire mutex cell;
  if choice = 1 then raise (Acquired choice)

let release_or_raise (mutex : Mutex.t) (cell : int ref) choice =
  if choice = 0 then raise Retained;
  release mutex cell;
  if choice = 1 then raise Released

let exceptional_acquire (mutex : Mutex.t) (cell : int ref) fail =
  if fail then (
    acquire mutex cell;
    raise (Acquired 1))

let acquire_with_defaults (mutex : Mutex.t) (cell : int ref) fail =
  if fail then raise (Unchanged 0);
  acquire mutex cell

let repeat (mutex : Mutex.t) (cell : int ref) =
  for i = 0 to 2 do
    acquire mutex cell;
    release mutex cell
  done

let client choice =
  let cell = ref 0 in
  let mutex = Mutex.create () in
  repeat mutex cell;
  try
    acquire_or_raise mutex cell choice;
    release mutex cell
  with
  | Acquired _ -> release mutex cell
  | Unchanged _ -> ()

let releasing_client choice =
  let cell = ref 0 in
  let mutex = Mutex.create () in
  acquire mutex cell;
  try release_or_raise mutex cell choice with
  | Retained -> release mutex cell
  | Released -> ()

let exceptional_client fail =
  let cell = ref 0 in
  let mutex = Mutex.create () in
  try exceptional_acquire mutex cell fail with Acquired _ -> release mutex cell
