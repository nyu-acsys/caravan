exception Stop

let count n =
  let i = ref 0 in
  while !i < n do
    if !i = 5 then raise Stop;
    incr i
  done;
  !i
(*@ r = count n
    requires n >= 0
    raises Stop *)
