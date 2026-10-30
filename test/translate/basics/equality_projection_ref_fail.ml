type wrapper = { value : int ref }

let claim (a : wrapper) (b : wrapper) = ()
(*@ claim a b requires a.value = b.value *)
