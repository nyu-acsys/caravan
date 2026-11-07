let rec rev_onto (xs : int list) acc =
  match xs with [] -> acc | x :: rest -> rev_onto rest (x :: acc)
(*@ r = rev_onto xs acc ensures List.length r = List.length xs + List.length acc *)
