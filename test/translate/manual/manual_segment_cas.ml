type node = End | Next of int * node Atomic.t

let replace (first : node Atomic.t) (limit : node Atomic.t) expected replacement =
  Atomic.compare_and_set first (Next (expected, limit)) (Next (replacement, limit))
(*@ Ghost.scope (fun step ->
  let previous = unfold singleton first limit {value} in
  let next = expose first limit previous in
  unfold segment next limit [];
  let success = step () in
  fold segment next limit [];
  if success then restore first limit replacement next
  else restore first limit previous next;
  fold singleton first limit {value = if success then replacement else previous};
  success)
*)
(*@ manual *)
(*@ result = replace first limit expected replacement
    requires singleton first limit
    ensures singleton first limit *)
