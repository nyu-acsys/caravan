exception Empty

val get : int list -> int
(*@ r = get xs
    ensures match xs with [] -> false | x :: _ -> r = x
    raises Empty -> xs = [] *)
