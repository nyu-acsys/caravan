let out_of_bounds () =
  let a = Array.make 3 0 in
  a.(3)

let negative () = Array.make (-1) true
let unowned (a : int array) = a.(0) <- 1
