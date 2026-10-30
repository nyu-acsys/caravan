let first (l : int list) = match l with x :: _ -> x
let f (l : int list) = 0
(*@ r = f l
    ensures r <= first l *)
