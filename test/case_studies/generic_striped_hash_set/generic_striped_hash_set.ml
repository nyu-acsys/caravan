(* A generic variant of the lock-striped hash set. *)
module type KEY = sig
  type t

  val equal : t -> t -> bool
  (*@ result = equal left right pure
      ensures result === (left === right) *)

  val hash : t -> int
  (*@ result = hash key pure
      ensures 0 <= result *)
end

module Make (Key : KEY) : sig
  type t = {
    locks : Mutex.t array;
    table : Key.t list array array Atomic.t;
    size : int Atomic.t;
  }

  (*@ invariant is_set (s : t) *)

  (*@ predicate contents (s : t) (values [@implicit] : Key.t finset) *)

  val create : int -> t
  (*@ result = create stripes
      requires 0 < stripes && stripes <= 1000 && Ghost.Mutex.context owner held
      ensures is_set result && contents result Finset.empty &&
        Ghost.Mutex.context owner held *)

  val contains : t -> Key.t -> bool
  (*@ result = atomic contains s x
      opens {is_set s}
      requires is_set s &&
        Ghost.Mutex.context owner held && held === Finset.empty
      ensures is_set s && Ghost.Mutex.context owner held
      atomic requires contents s before
      atomic ensures contents s before && result === Finset.mem x before *)

  val add : t -> Key.t -> bool
  (*@ result = atomic add s x
      opens {is_set s}
      requires is_set s &&
        Ghost.Mutex.context owner held && held === Finset.empty
      ensures is_set s && Ghost.Mutex.context owner held
      atomic requires contents s before
      atomic ensures contents s (Finset.union before (Finset.singleton x)) &&
        result === not (Finset.mem x before) *)

  val remove : t -> Key.t -> bool
  (*@ result = atomic remove s x
      opens {is_set s}
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
      opens {is_set s}
      requires is_set s && 0 < old_capacity &&
        Ghost.Mutex.context owner held && held === Finset.empty
      ensures is_set s && Ghost.Mutex.context owner held *)
end = struct
  type t = {
    locks : Mutex.t array;
    table : Key.t list array array Atomic.t;
    size : int Atomic.t;
  }

  let rec mem (x : Key.t) bucket =
    match bucket with [] -> false | y :: rest -> Key.equal y x || mem x rest

  let rec without (x : Key.t) bucket =
    match bucket with
    | [] -> []
    | y :: rest -> if Key.equal y x then without x rest else y :: without x rest

  let create stripes =
    let rows = Array.make stripes (Array.make 1 []) in
    let table = Atomic.make rows in
    let locks = Array.make stripes (Mutex.create ()) in
    for i = 0 to stripes - 1 do
      rows.(i) <- Array.make 1 [];
      locks.(i) <- Mutex.create ()
    done;
    { locks; table; size = Atomic.make 0 }

  let[@inline] stripe_count s = Array.length s.locks
  let[@inline] bucket_index hash stripes capacity = hash / stripes mod capacity

  let contains s x =
    let stripes = stripe_count s in
    let hash = Key.hash x in
    let stripe = hash mod stripes in
    let lock = s.locks.(stripe) in
    Mutex.lock lock;
    let row = (Atomic.get s.table).(stripe) in
    let result = mem x row.(bucket_index hash stripes (Array.length row)) in
    Mutex.unlock lock;
    result

  let remove s x =
    let stripes = stripe_count s in
    let hash = Key.hash x in
    let stripe = hash mod stripes in
    let lock = s.locks.(stripe) in
    Mutex.lock lock;
    let row = (Atomic.get s.table).(stripe) in
    let bucket = bucket_index hash stripes (Array.length row) in
    let removed = mem x row.(bucket) in
    if removed then row.(bucket) <- without x row.(bucket);
    Mutex.unlock lock;
    if removed then Atomic.decr s.size;
    removed

  let rec rehash row capacity stripes bucket =
    match bucket with
    | [] -> ()
    | x :: rest ->
        let hash = Key.hash x in
        let target = bucket_index hash stripes capacity in
        row.(target) <- x :: row.(target);
        rehash row capacity stripes rest

  let empty_row capacity = Array.make capacity []

  let rebuild old_row capacity stripes =
    let row = empty_row capacity in
    for k = 0 to Array.length old_row - 1 do
      rehash row capacity stripes old_row.(k)
    done;
    row

  let resize_locked s old_capacity =
    let stripes = stripe_count s in
    let old_table = Atomic.get s.table in
    let growing =
      Array.length old_table.(0) = old_capacity && old_capacity <= 9007199254740991
    in
    if growing then begin
      let capacity = 2 * old_capacity in
      let table = Array.make stripes (Array.make 1 []) in
      for i = 0 to stripes - 1 do
        let row = rebuild old_table.(i) capacity stripes in
        table.(i) <- row
      done;
      Atomic.set s.table table
    end

  let resize s old_capacity =
    let stripes = stripe_count s in
    for i = 0 to stripes - 1 do
      Mutex.lock s.locks.(i)
    done;
    resize_locked s old_capacity;
    for i = 0 to stripes - 1 do
      Mutex.unlock s.locks.(i)
    done

  let add s x =
    let stripes = stripe_count s in
    let hash = Key.hash x in
    let stripe = hash mod stripes in
    let lock = s.locks.(stripe) in
    Mutex.lock lock;
    let row = (Atomic.get s.table).(stripe) in
    let capacity = Array.length row in
    let bucket = bucket_index hash stripes capacity in
    let added = not (mem x row.(bucket)) in
    if added then row.(bucket) <- x :: row.(bucket);
    Mutex.unlock lock;
    if added then begin
      Atomic.incr s.size;
      (* The load factor policy: more than four elements per bucket. *)
      if Atomic.get s.size / stripes / capacity > 4 then resize s capacity
    end;
    added
end
