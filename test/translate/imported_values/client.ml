let pair () =
  let first : int Constants.t = Constants.empty in
  let second : int Constants.t = Constants.empty in
  (first, second)

let number () = Constants.zero
let unit_value () = Constants.token
let local_value () = Operations.make 17

let inspect cell =
  let result = Atomic.get cell in
  Operations.no_step ();
  result
