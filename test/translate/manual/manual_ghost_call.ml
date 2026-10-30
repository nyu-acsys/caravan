let read_known (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
    let result = step () in
    result) *)
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [seen : int] = read_known [expected : int] cell
    requires own cell expected
    ensures own cell expected && result = seen && seen = expected *)

let use_known (cell : int Atomic.t) = read_known cell
(*@ Ghost.scope (fun invoke ->
    let (result, seen) = invoke 7 in
    assert (result = seen);
    result) *)
(*@ manual *)
(*@ result = use_known cell
    requires own cell 7
    ensures own cell 7 && result = 7 *)

let use_current_state (cell : int Atomic.t) =
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, result)) *)
  in
  read_known cell
(*@ Ghost.State.scope (fun invoke (expected : int) ->
    let (result, seen) = invoke expected in
    assert (result = seen);
    (result, seen)) *)
(*@ manual *)
(*@ result = use_current_state cell
    requires own cell 7
    ensures own cell 7 && result = 7 *)

let exchange_pair (cell : int Atomic.t) next =
  let previous =
    Atomic.exchange cell next
    (*@ Ghost.scope (fun step ->
      let result = step () in
      result) *)
  in
  (previous, next)
(*@ Ghost.returns (fun result () ->
    match result with (previous, latest) -> (previous, latest)) *)
(*@ manual *)
(*@ result, [seen_before : int], [seen_after : int] =
      exchange_pair [expected : int] cell next
    requires own cell expected
    ensures own cell next && result = (expected, next)
      && seen_before = expected && seen_after = next *)

let use_exchange_pair (cell : int Atomic.t) = exchange_pair cell 8
(*@ Ghost.scope (fun invoke ->
    let (result, (before, after)) = invoke 7 in
    assert (result = (before, after));
    result) *)
(*@ manual *)
(*@ result = use_exchange_pair cell
    requires own cell 7
    ensures own cell 8 && result = (7, 8) *)

let add_hint value = value + 1
(*@ result = add_hint [hint : int] value
    requires hint = value && hint < max_int
    ensures result = hint + 1 *)

let use_hint value = add_hint value
(*@ Ghost.scope (fun invoke ->
    let result = invoke value in
    result) *)
(*@ manual *)
(*@ result = use_hint value
    requires value < max_int
    ensures result = value + 1 *)

let duplicate (value : int) = value
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [copy : int] = duplicate value
    ensures result = copy && copy = value *)

let use_duplicate value = duplicate value
(*@ Ghost.scope (fun invoke ->
    let (result, copy) = invoke () in
    assert (result = copy);
    result) *)
(*@ manual *)
(*@ result = use_duplicate value ensures result = value *)

let with_two_hints left right = left + right
(*@ result = with_two_hints [first : int] [second : int] left right
    requires first = left && second = right
      && 0 <= first && 0 <= second && first <= max_int - second
    ensures result = first + second *)

let use_two_hints left right = with_two_hints left right
(*@ Ghost.scope (fun invoke ->
    let result = invoke (left, right) in
    result) *)
(*@ manual *)
(*@ result = use_two_hints left right
    requires 0 <= left && 0 <= right && left <= max_int - right
    ensures result = left + right *)

let choose flag (left : int) (right : int) =
  if flag then left (*@ Ghost.returns (fun result () -> result) *) else right
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [copy : int] = choose flag left right
    ensures result = copy && result = (if flag then left else right) *)

let use_choose flag left right = choose flag left right
(*@ Ghost.scope (fun invoke ->
    let (result, copy) = invoke () in
    assert (result = copy);
    result) *)
(*@ manual *)
(*@ result = use_choose flag left right
    ensures result = if flag then left else right *)

let copy_pair (value : int) = (value, value)
(*@ Ghost.returns (fun result () -> result) *)
(*@ manual *)
(*@ result, [copy : int * int] = copy_pair value
    ensures result = copy && copy = (value, value) *)

let use_copy_pair value = copy_pair value
(*@ Ghost.scope (fun invoke ->
    let (result, copy) = invoke () in
    assert (result = copy);
    result) *)
(*@ manual *)
(*@ result = use_copy_pair value ensures result = (value, value) *)

let unit_marker (value : int) = value
(*@ Ghost.returns (fun result () -> ()) *)
(*@ manual *)
(*@ result, [marker : unit] = unit_marker value
    ensures result = value && marker = () *)

let use_unit_marker value = unit_marker value
(*@ Ghost.scope (fun invoke ->
    let (result, marker) = invoke () in
    assert (marker = ());
    result) *)
(*@ manual *)
(*@ result = use_unit_marker value ensures result = value *)

let store_known (cell : int Atomic.t) next = Atomic.set cell next
(*@ Ghost.scope (fun step ->
    let result = step () in
    result) *)
(*@ Ghost.returns (fun result () -> next) *)
(*@ manual *)
(*@ result, [stored : int] = store_known [expected : int] cell next
    requires own cell expected
    ensures own cell next && stored = next *)

let use_store_known (cell : int Atomic.t) = store_known cell 8
(*@ Ghost.scope (fun invoke ->
    let (result, stored) = invoke 7 in
    assert (result = ());
    assert (stored = 8);
    result) *)
(*@ manual *)
(*@ result = use_store_known cell
    requires own cell 7
    ensures own cell 8 && result = () *)

let read_with_state_return (cell : int Atomic.t) =
  let _ =
    Atomic.get cell
    (*@ Ghost.State.scope (fun step () ->
      let result = step () in
      (result, result)) *)
  in
  Atomic.get cell
(*@ Ghost.State.scope (fun step (saved : int) ->
    let result = step () in
    assert (result = saved);
    (result, saved)) *)
(*@ Ghost.returns (fun result (saved : int) -> saved) *)
(*@ manual *)
(*@ result, [copy : int] = read_with_state_return [expected : int] cell
    requires own cell expected
    ensures own cell expected && result = copy && copy = expected *)

let use_state_return (cell : int Atomic.t) = read_with_state_return cell
(*@ Ghost.scope (fun invoke ->
    let (result, copy) = invoke 7 in
    assert (result = copy);
    result) *)
(*@ manual *)
(*@ result = use_state_return cell
    requires own cell 7
    ensures own cell 7 && result = 7 *)

let echo_runtime (value : int) = value
(*@ result = echo_runtime [source : int] value
    requires source = value
    ensures result = source *)

let use_evaluated_once (counter : int Atomic.t) =
  echo_runtime
    (Atomic.fetch_and_add counter
       1 (*@ Ghost.scope (fun step ->
       let result = step () in
       result) *))
(*@ Ghost.scope (fun invoke ->
    let result = invoke before in
    assert (result = before);
    result) *)
(*@ manual *)
(*@ result = use_evaluated_once counter
    requires own counter before && before < max_int
    ensures own counter (before + 1) && result = before *)

let echo_pair (pair : int * int) = pair
(*@ result = echo_pair [hint : int * int] pair
    requires hint = pair
    ensures result = hint *)

let use_tuple_hint () = echo_pair (7, 8)
(*@ Ghost.scope (fun invoke ->
    let result = invoke (7, 8) in
    assert (result = (7, 8));
    result) *)
(*@ manual *)
(*@ result = use_tuple_hint () ensures result = (7, 8) *)

let use_right_to_left (counter : int Atomic.t) =
  with_two_hints
    (Atomic.fetch_and_add counter
       1 (*@ Ghost.scope (fun step ->
       let result = step () in
       result) *))
    (Atomic.fetch_and_add counter
       1 (*@ Ghost.scope (fun step ->
       let result = step () in
       result) *))
(*@ Ghost.scope (fun invoke ->
    let result = invoke (8, 7) in
    assert (result = 15);
    result) *)
(*@ manual *)
(*@ result = use_right_to_left counter
    requires own counter 7
    ensures own counter 9 && result = 15 *)

let lexical_hint (value : int) =
  let hint = value in
  let _ =
    let hint = 0 in
    ()
  in
  echo_runtime value
(*@ Ghost.scope (fun invoke ->
    let result = invoke hint in
    result) *)
(*@ manual *)
(*@ result = lexical_hint value ensures result = value *)

let lexical_return (value : int) =
  let hint = value in
  let _ =
    let hint = 0 in
    ()
  in
  value
(*@ Ghost.returns (fun result () -> hint) *)
(*@ manual *)
(*@ result, [copy : int] = lexical_return value
    ensures result = value && copy = value *)
