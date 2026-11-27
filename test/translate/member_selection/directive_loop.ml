let good () = ()

let loop n =
# 1 "selection_loop_virtual.ml"
  let counter = ref 0 in
  while !counter < n do
    (*@ invariant own counter.contents value && value <= 0 *)
    incr counter
  done
(*@ loop n requires 0 <= n <= 1000 *)
