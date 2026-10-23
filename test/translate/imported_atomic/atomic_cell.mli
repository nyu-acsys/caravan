type t

(*@ invariant shared (cell : t) *)
(*@ predicate holds (cell : t) (value [@implicit] : int) *)
(*@ predicate ticket (cell : t) (count : int) *)

val make : int -> t
(*@ cell = make value
    ensures shared cell && holds cell value && ticket cell 0 *)

val read : t -> int
(*@ result = atomic read cell
    requires shared cell && ticket cell count
    ensures ticket cell count
    atomic requires holds cell value
    atomic ensures holds cell value && result = value *)

val replace : t -> int -> unit
(*@ result = atomic replace cell value
    requires shared cell && ticket cell count
    ensures ticket cell count && result = ()
    atomic requires holds cell previous
    atomic ensures holds cell value && result = () *)

val forget : t -> unit
(*@ atomic forget cell
    requires shared cell
    atomic requires holds cell previous
    atomic ensures holds cell current *)

val read_pair : t -> int * bool
(*@ result = atomic read_pair cell
    requires shared cell && ticket cell count
    ensures ticket cell count
    atomic requires holds cell value
    atomic ensures holds cell value && result = (value, true) *)

(*@ invariant versioned (cell : t) (version : int) *)

val observe_version : t -> int -> unit
(*@ atomic observe_version cell version
    requires versioned cell version
    atomic requires true
    atomic ensures true *)
