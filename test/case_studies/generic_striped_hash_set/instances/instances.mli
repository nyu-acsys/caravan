module Integer_key : sig
  type t = int

  val equal : t -> t -> bool
  (*@ result = equal left right pure
      ensures result === (left === right) *)

  val hash : t -> int
  (*@ result = hash key pure
      ensures 0 <= result *)
end

module Integer_set : sig
  type t

  (*@ invariant is_set (s : t) *)

  (*@ predicate contents (s : t) (values [@implicit] : Integer_key.t finset) *)

  val create : int -> t
  (*@ result = create stripes
      requires 0 < stripes && stripes <= 1000 && Ghost.Mutex.context owner held
      ensures is_set result && contents result Finset.empty &&
        Ghost.Mutex.context owner held *)

  val contains : t -> Integer_key.t -> bool
  (*@ result = atomic contains s x
      requires is_set s &&
        Ghost.Mutex.context owner held && held === Finset.empty
      ensures is_set s && Ghost.Mutex.context owner held
      atomic requires contents s before
      atomic ensures contents s before && result === Finset.mem x before *)

  val add : t -> Integer_key.t -> bool
  (*@ result = atomic add s x
      requires is_set s &&
        Ghost.Mutex.context owner held && held === Finset.empty
      ensures is_set s && Ghost.Mutex.context owner held
      atomic requires contents s before
      atomic ensures contents s (Finset.union before (Finset.singleton x)) &&
        result === not (Finset.mem x before) *)

  val remove : t -> Integer_key.t -> bool
  (*@ result = atomic remove s x
      requires is_set s &&
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
end

module Record_key : sig
  type t = { number : int; flag : bool }

  val equal : t -> t -> bool
  (*@ result = equal left right pure
      ensures result === (left === right) *)

  val hash : t -> int
  (*@ result = hash key pure
      ensures 0 <= result *)
end

module Record_set : sig
  type t

  (*@ invariant is_set (s : t) *)

  (*@ predicate contents (s : t) (values [@implicit] : Record_key.t finset) *)

  val create : int -> t
  (*@ result = create stripes
      requires 0 < stripes && stripes <= 1000 && Ghost.Mutex.context owner held
      ensures is_set result && contents result Finset.empty &&
        Ghost.Mutex.context owner held *)

  val contains : t -> Record_key.t -> bool
  (*@ result = atomic contains s x
      requires is_set s &&
        Ghost.Mutex.context owner held && held === Finset.empty
      ensures is_set s && Ghost.Mutex.context owner held
      atomic requires contents s before
      atomic ensures contents s before && result === Finset.mem x before *)

  val add : t -> Record_key.t -> bool
  (*@ result = atomic add s x
      requires is_set s &&
        Ghost.Mutex.context owner held && held === Finset.empty
      ensures is_set s && Ghost.Mutex.context owner held
      atomic requires contents s before
      atomic ensures contents s (Finset.union before (Finset.singleton x)) &&
        result === not (Finset.mem x before) *)

  val remove : t -> Record_key.t -> bool
  (*@ result = atomic remove s x
      requires is_set s &&
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
end

module Reference_key : sig
  type t = int ref

  val equal : t -> t -> bool
  (*@ result = equal left right pure
      ensures result === (left === right) *)

  val hash : t -> int
  (*@ result = hash key pure
      ensures 0 <= result *)
end

module Reference_set : sig
  type t

  (*@ invariant is_set (s : t) *)

  (*@ predicate contents (s : t) (values [@implicit] : Reference_key.t finset) *)

  val create : int -> t
  (*@ result = create stripes
      requires 0 < stripes && stripes <= 1000 && Ghost.Mutex.context owner held
      ensures is_set result && contents result Finset.empty &&
        Ghost.Mutex.context owner held *)

  val contains : t -> Reference_key.t -> bool
  (*@ result = atomic contains s x
      requires is_set s &&
        Ghost.Mutex.context owner held && held === Finset.empty
      ensures is_set s && Ghost.Mutex.context owner held
      atomic requires contents s before
      atomic ensures contents s before && result === Finset.mem x before *)

  val add : t -> Reference_key.t -> bool
  (*@ result = atomic add s x
      requires is_set s &&
        Ghost.Mutex.context owner held && held === Finset.empty
      ensures is_set s && Ghost.Mutex.context owner held
      atomic requires contents s before
      atomic ensures contents s (Finset.union before (Finset.singleton x)) &&
        result === not (Finset.mem x before) *)

  val remove : t -> Reference_key.t -> bool
  (*@ result = atomic remove s x
      requires is_set s &&
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
end
