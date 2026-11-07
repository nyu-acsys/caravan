let ( +. ) (x : int) (_y : int) = x
let client () = ()
(*@ client () ensures 0 +. 0 = 0 *)
