val acquire : Mutex.t -> unit
(*@ acquire mutex
    requires Ghost.Mutex.context owner held && not (Finset.mem mutex held)
    ensures Ghost.Mutex.context owner (Finset.union held (Finset.singleton mutex)) *)

module Nested : sig
  val release : Mutex.t -> unit
  (*@ release mutex
      requires Ghost.Mutex.context owner held && Finset.mem mutex held
      ensures Ghost.Mutex.context owner (Finset.diff held (Finset.singleton mutex)) *)
end
