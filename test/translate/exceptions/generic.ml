exception Empty

let head xs = match xs with [] -> raise Empty | x :: _ -> x

(*@ r = head xs
    ensures match xs with [] -> false | x :: _ -> r === x
    raises Empty -> xs = [] *)
let both (a : int list) (b : bool list) = (head a, head b)
(*@ r = both a b
    raises Empty -> a = [] || b = [] *)
