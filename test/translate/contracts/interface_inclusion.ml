type t = int

let create (value : int) = value
let get (value : t) = value
let identity value = value
let private_helper (value : bool) = not value
