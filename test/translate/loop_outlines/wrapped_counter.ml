let increment cell = incr cell

let count cell =
  for i = 0 to 9 do
    increment cell
  done
