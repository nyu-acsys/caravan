type t

(*@ invariant root (cell : t) *)
(*@ invariant [@within root cell] leaf (cell : t) *)

val peek : t -> int
(*@ result = peek cell
    requires leaf cell
    ensures leaf cell
    opens {leaf cell} *)
