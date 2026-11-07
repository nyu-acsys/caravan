let outer value =
  let helper item = (value, item) in
  (*@ result = helper item ensures result === (value, item) *)
  (helper true, helper 17)
(*@ result = outer value ensures result === ((value, true), (value, 17)) *)

let independent value =
  let helper item =
    let _ = value in
    item
  in
  (*@ result = helper item ensures result === item *)
  (helper true, helper 17)
(*@ result = independent value ensures result === (true, 17) *)

let clients () =
  assert (outer 23 = ((23, true), (23, 17)));
  assert (outer false = ((false, true), (false, 17)));
  assert (independent 23 = (true, 17));
  assert (independent false = (true, 17))
