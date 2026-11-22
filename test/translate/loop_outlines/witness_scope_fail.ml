type box = { mutable v : int }

let fill (a : int array) (b : box) =
  b.v <- 0;
  for i = 0 to Array.length a - 1 do
    a.(i) <- i
  done
