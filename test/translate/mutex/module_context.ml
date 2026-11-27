module type Operations = sig
  (*@ predicate contents (cell : int Atomic.t) (value [@implicit] : int) *)
  val acquire : Mutex.t -> unit
  (*@ acquire mutex
      requires Ghost.Mutex.context who locks && not (Finset.mem mutex locks) && Guard.is_mutex mutex ()
      ensures Ghost.Mutex.context who (Finset.union locks (Finset.singleton mutex)) &&
        Guard.is_mutex mutex () && Guard.held mutex who && Resource.resource () *)

  val release : Mutex.t -> unit
  (*@ release mutex
      requires Ghost.Mutex.context who locks && Finset.mem mutex locks &&
        Guard.is_mutex mutex () && Guard.held mutex who && Resource.resource ()
      ensures Ghost.Mutex.context who (Finset.diff locks (Finset.singleton mutex)) && Guard.is_mutex mutex () *)

  val check : unit -> unit
  (*@ check () ensures true *)

  val read : int Atomic.t -> int
  (*@ result = atomic read cell
      requires Ghost.Mutex.context who locks
      atomic requires contents cell value
      atomic ensures contents cell value && result === value *)
end

module Actual = struct
  let acquire (mutex : Mutex.t) = Mutex.lock mutex
  let release (mutex : Mutex.t) = Mutex.unlock mutex
  let check () = ()
  let read (cell : int Atomic.t) = Atomic.get cell
  (*@ result = atomic read cell
      atomic requires contents cell value
      atomic ensures contents cell value && result === value *)
end

module Checked : Operations = Actual
module Again : Operations = Checked

module Use (O : Operations) = struct
  let run mutex cell =
    O.check ();
    O.acquire mutex;
    O.release mutex;
    O.read cell
  (*@ result = run mutex cell
      requires Ghost.Mutex.context self held && not (Finset.mem mutex held) &&
        Guard.is_mutex mutex () && O.contents cell 7
      ensures Guard.is_mutex mutex () && O.contents cell 7 && result === 7 *)
end

module First = Use (Checked)
module Second = Use (Again)

let client () =
  let mutex = Mutex.create () in
  let cell = Atomic.make 7 in
  let first = First.run mutex cell in
  let second = Second.run mutex cell in
  first + second
