type t = {
  locks : Mutex.t array;
  table : int list array array Atomic.t;
  size : int Atomic.t;
}
(** A resizable lock-striped set of nonnegative integers. *)

(*@ invariant is_set (s : t) *)

(*@ predicate contents (s : t) (values [@implicit] : int finset) *)

val create : int -> t
(*@ result = create stripes
    requires 0 < stripes && stripes <= 1000 && Ghost.Mutex.context owner held
    ensures is_set result && contents result Finset.empty &&
      Ghost.Mutex.context owner held *)

val contains : t -> int -> bool
(*@ result = atomic contains s x
    requires is_set s && 0 <= x &&
      Ghost.Mutex.context owner held && held === Finset.empty
    ensures is_set s && Ghost.Mutex.context owner held
    atomic requires contents s before
    atomic ensures contents s before && result === Finset.mem x before *)

val add : t -> int -> bool
(*@ result = atomic add s x
    requires is_set s && 0 <= x &&
      Ghost.Mutex.context owner held && held === Finset.empty
    ensures is_set s && Ghost.Mutex.context owner held
    atomic requires contents s before
    atomic ensures contents s (Finset.union before (Finset.singleton x)) &&
      result === not (Finset.mem x before) *)

val remove : t -> int -> bool
(*@ result = atomic remove s x
    requires is_set s && 0 <= x &&
      Ghost.Mutex.context owner held && held === Finset.empty
    ensures is_set s && Ghost.Mutex.context owner held
    atomic requires contents s before
    atomic ensures contents s (Finset.diff before (Finset.singleton x)) &&
      result === Finset.mem x before *)

val resize : t -> int -> unit
(** Double the rows when the first row still has the requested capacity and the new
    capacity fits an OCaml array. Stale or oversized requests leave it alone. *)
(*@ resize s old_capacity
    requires is_set s && 0 < old_capacity &&
      Ghost.Mutex.context owner held && held === Finset.empty
    ensures is_set s && Ghost.Mutex.context owner held *)
