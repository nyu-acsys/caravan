exception Empty

let head (xs : int list) = match xs with [] -> raise Empty | x :: _ -> x
(*@ r = head xs
    ensures match xs with [] -> false | x :: _ -> r = x
    raises Empty -> xs = [] *)

let head_or xs d = try head xs with Empty -> d
(*@ r = head_or xs d
    ensures r <> d *)
