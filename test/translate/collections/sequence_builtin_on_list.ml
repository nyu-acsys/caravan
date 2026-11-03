let rec rev_onto (xs : int list) acc =
  match xs with [] -> acc | x :: rest -> rev_onto rest (x :: acc)
(*@ r = rev_onto xs acc ensures length r = length xs + length acc *)
