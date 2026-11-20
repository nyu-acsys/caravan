val create : unit -> int
(*@ result = create () ensures result = 8 *)

val swap : int array -> int -> int -> unit
(*@ swap a i j
    requires 0 <= i && i < Array.length a && 0 <= j && j < Array.length a && i <> j
    requires own (Array.cell a i) x && own (Array.cell a j) y
    ensures own (Array.cell a i) y && own (Array.cell a j) x *)

val clear : int array -> unit
(*@ clear a
    requires forall j : int. 0 <= j && j < Array.length a ->
      exists v : int. own (Array.cell a j) v
    ensures forall j : int. 0 <= j && j < Array.length a -> own (Array.cell a j) 0 *)

val first : 'a array -> 'a
(*@ result = first a
    requires 0 < Array.length a && own (Array.cell a 0) v
    ensures own (Array.cell a 0) v && result === v *)
