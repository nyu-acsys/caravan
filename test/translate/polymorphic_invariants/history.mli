type 'a t

(*@ invariant live (root : 'a t) *)
(*@ predicate contents (root : 'a t) (value : 'a) *)

val create : 'a -> 'a t
(*@ root = create value ensures live root && contents root value *)

val remember : 'a t -> 'a t -> unit
(*@ remember root cell
    requires live root
    requires past (mem cell s.cells)
    ensures live root
    ensures past (mem cell s.cells) *)

val forward : 'a t -> 'a t -> unit
(*@ forward root cell
    requires live root
    requires past (mem cell s.cells)
    ensures live root
    ensures past (mem cell s.cells) *)

val integers : int t -> int t -> unit
(*@ integers root cell
    requires live root
    requires past (mem cell s.cells)
    ensures live root
    ensures past (mem cell s.cells) *)

val booleans : bool t -> bool t -> unit
(*@ booleans root cell
    requires live root
    requires past (mem cell s.cells)
    ensures live root
    ensures past (mem cell s.cells) *)

val mixed : int t -> int t -> bool t -> bool t -> unit
(*@ mixed left left_cell right right_cell
    requires live left && live right
    requires past (mem left_cell s.cells)
    requires past (mem right_cell s.cells)
    ensures live left && live right
    ensures past (mem left_cell s.cells)
    ensures past (mem right_cell s.cells) *)
