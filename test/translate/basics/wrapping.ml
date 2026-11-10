let add_boundary () = max_int + 1
(*@ result = add_boundary () ensures result = min_int *)

let subtract_boundary () = min_int - 1
(*@ result = subtract_boundary () ensures result = max_int *)

let negate_boundary () = -min_int
(*@ result = negate_boundary () ensures result = min_int *)

let multiply_boundary () = max_int * max_int
(*@ result = multiply_boundary () ensures result = 1 *)

let multiply_minimum () = min_int * min_int
(*@ result = multiply_minimum () ensures result = 0 *)

let quotient_boundary () = min_int / -1
(*@ result = quotient_boundary () ensures result = min_int *)

let remainder_boundary () = min_int mod -1
(*@ result = remainder_boundary () ensures result = 0 *)

let signed_division () = (-7 / 2, 7 / -2, -7 / -2, -7 mod 2, 7 mod -2)
(*@ result = signed_division () ensures result = (-3, -3, 3, -1, 1) *)

let nested_comparison () = max_int + 1 < 0
(*@ result = nested_comparison () ensures result *)

let nested_division () = (max_int + 1) / 2
(*@ result = nested_division () ensures result = min_int / 2 *)

let nested_product () = (max_int * max_int) + max_int
(*@ result = nested_product () ensures result = min_int *)

let increment_boundary () =
  let cell = ref max_int in
  incr cell;
  !cell
(*@ result = increment_boundary () ensures result = min_int *)

let decrement_boundary () =
  let cell = ref min_int in
  decr cell;
  !cell
(*@ result = decrement_boundary () ensures result = max_int *)

let next value = value + 1
(*@ result = next value pure
    ensures if value = max_int then result = min_int else result = value + 1 *)

let pure_calls () = next max_int
(*@ result = pure_calls ()
    ensures result = min_int && next max_int = min_int
    ensures max_int + 1 > max_int *)

let upper_bound_loop () =
  let count = ref 0 in
  for i = max_int to max_int do
    (*@ invariant own count.contents (i - max_int) *)
    assert (i = max_int);
    incr count
  done;
  !count
(*@ result = upper_bound_loop () ensures result = 1 *)

let lower_bound_loop () =
  let count = ref 0 in
  for i = min_int downto min_int do
    (*@ invariant own count.contents (min_int - i) *)
    assert (i = min_int);
    incr count
  done;
  !count
(*@ result = lower_bound_loop () ensures result = 1 *)

let multiply left right = left * right
(*@ result = multiply left right
    ensures min_int <= result && result <= max_int *)

let cancel_increment value = value + 1 - 1
(*@ result = cancel_increment value ensures result = value *)

let while_guard () =
  let count = ref 0 in
  while max_int + 1 >= 0 do
    (*@ invariant own count.contents 0 *)
    incr count
  done;
  !count
(*@ result = while_guard () ensures result = 0 *)
