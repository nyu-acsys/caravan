let f n =
  let c = ref n in
  while !c > 0 do
    (*@ invariant own c.contents k
        variant k *)
    decr c
  done
