let choose fallback values =
  let helper items = match items with [] -> fallback | head :: _ -> head in
  helper values
(*@ result = choose fallback values pure
    ensures match values with [] -> result === fallback | head :: _ -> result === head *)

let capture_pair (value, flag) =
  let captured = (value, flag) in
  let helper () = captured in
  helper ()
(*@ result = capture_pair pair pure ensures result === pair *)

let last fallback values =
  let rec helper items =
    match items with
    | [] -> fallback
    | head :: tail -> ( match tail with [] -> head | _ :: _ -> helper tail)
  in
  helper values
(*@ result = last fallback values pure
    ensures values === [] -> result === fallback *)

let integers () =
  assert (choose 17 [] = 17);
  assert (choose 17 [ 23 ] = 23);
  assert (capture_pair (17, true) = (17, true));
  assert (last 17 [] = 17)

let booleans () =
  assert (choose true []);
  assert (not (choose true [ false ]));
  assert (capture_pair (true, 17) = (true, 17));
  assert (not (last false []))
