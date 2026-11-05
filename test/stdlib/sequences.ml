let roundtrip () =
  let sequence = List.to_seq [ 1; 2; 3 ] in
  assert (List.of_seq sequence = [ 1; 2; 3 ]);
  assert (List.of_seq sequence = [ 1; 2; 3 ])

let empty () =
  assert (List.of_seq Seq.empty = ([] : int list));
  assert (List.of_seq Seq.empty = ([] : bool list))

let booleans () =
  let sequence = List.to_seq [ true; false ] in
  assert (List.of_seq sequence = [ true; false ])
