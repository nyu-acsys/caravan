exception Empty

let pick (xs : int list) = match xs with [] -> raise Empty | x :: _ -> x
let lookup (xs : int list) = match xs with [] -> raise Not_found | _ -> pick xs
(*@ r = lookup xs
    raises Not_found -> xs = []
    raises Empty *)
