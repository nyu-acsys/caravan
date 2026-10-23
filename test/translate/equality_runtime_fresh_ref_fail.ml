let compare_refs () =
  let left = ref 0 in
  let right = ref 0 in
  left = right
(*@ result = compare_refs () ensures result = false *)
