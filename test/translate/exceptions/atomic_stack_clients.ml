let catching_client () =
  let stack = create () in
  push stack 17;
  let first = pop_exn stack in
  let second = try pop_exn stack with Empty -> 0 in
  assert (first = 17);
  assert (second = 0)

let propagating_client (s : int t) = pop_exn s
(*@ r = propagating_client s
    requires stack s xs
    ensures match xs with [] -> false | x :: xs' -> r = x && stack s xs'
    raises Empty -> xs = [] && stack s [] *)
