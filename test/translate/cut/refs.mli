val keep : int ref -> int ref -> int
(*@ result = keep r s
    requires own r.contents a && own s.contents b
    ensures own r.contents 3 && result = 3 *)

val read_restated : int ref -> int
(*@ result = read_restated r
    requires own r.contents a
    ensures own r.contents 3 && result = a *)
