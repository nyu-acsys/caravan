exception Empty

let head (xs : int list) = match xs with [] -> raise Empty | x :: _ -> x
(*@ r = head xs
    raises Empty -> xs <> [] *)
