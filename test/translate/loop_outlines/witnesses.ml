let fill (a : int array) =
  for i = 0 to Array.length a - 1 do
    a.(i) <- i
  done
