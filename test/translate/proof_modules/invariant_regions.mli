type t

(*@ invariant root (cell : t) *)

val create : unit -> t
(*@ result = create () ensures root result *)

val get : t -> int
(*@ result = get cell
    requires root cell
    ensures root cell && result === 0
    opens {root cell} *)
