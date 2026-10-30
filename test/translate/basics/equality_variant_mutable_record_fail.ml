type cell = { mutable value : int }
type wrapper = Wrapped of cell

let claim (a : wrapper) (b : wrapper) = ()
(*@ claim a b requires a = b *)
