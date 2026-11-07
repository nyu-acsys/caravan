type cell = { mutable value : int }

let claim (a : cell list) (b : cell list) = ()
(*@ claim a b requires a = b *)
