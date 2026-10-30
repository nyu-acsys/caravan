type pair = { left : int ref; right : int }

let claim (a : pair) (b : pair) = ()
(*@ claim a b requires a = b *)
