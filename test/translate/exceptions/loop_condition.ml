exception Stop

let positive n = if n <= 0 then raise Stop else true
(*@ b = positive n
    raises Stop -> n <= 0 *)

let count n =
  let i = ref n in
  while positive !i do
    (*@ invariant own i.contents k *)
    decr i
  done
(*@ count n
    requires n < 1000
    raises Stop *)
