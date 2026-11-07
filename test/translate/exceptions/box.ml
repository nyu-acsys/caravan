exception Empty

let get xs = match xs with [] -> raise Empty | x :: _ -> x
