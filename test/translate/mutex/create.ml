module Native = Mutex

type handle = Native.t
type holder = { mutex : handle }

let identity (mutex : handle) = mutex
(*@ result = identity mutex ensures result === mutex *)

let create () =
  let mutex = Native.create () in
  let alias = identity mutex in
  assert (mutex == alias);
  { mutex = alias }
(*@ result = create () ensures result.mutex === result.mutex *)

let argument () =
  let cell = ref 0 in
  let _mutex = Mutex.create (cell := 1) in
  !cell
(*@ result = argument () ensures result === 1 *)

let id value = value
(*@ result = id value ensures result === value *)

let polymorphic () =
  let mutex = Mutex.create () in
  let alias = id mutex in
  assert (mutex == alias);
  alias
(*@ result = polymorphic () ensures true *)

module Maker (A : sig
  type t
end) =
struct
  let make (value : A.t) = (Mutex.create (), value)
  (*@ result = make value ensures let (_mutex, returned) = result in returned === value *)
end

module Int = struct
  type t = int
end

module Make = Maker (Int)

let applied () =
  let mutex, value = Make.make 7 in
  assert (mutex == mutex);
  value
(*@ result = applied () ensures result === 7 *)

module Mutex = struct
  type t = int

  let create () = 4

  (*@ result = create () ensures result === 4 *)
  let lock value = value + 1
  (*@ result = lock value requires value === 4 ensures result === 5 *)
end

let shadow () = Mutex.lock (Mutex.create ())
(*@ result = shadow () ensures result === 5 *)
