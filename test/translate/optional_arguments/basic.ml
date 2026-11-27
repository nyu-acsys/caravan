let supplied ?value () = value
let choose ?(value = 42) () = value
let forward ?value () = choose ?value ()
let alias = choose
let fallback first ?(value = first) () = value
let chained ?(first = 1) ?(second = first + 1) () = (first, second)
let pair ?pair:(left, right = (1, 2)) () = (left, right)
let twice ?(value = 21) () = value + value
(*@ result = twice value token pure
    requires (match value with None -> true | Some v -> 0 <= v && v <= 100)
    ensures result = 2 * (match value with None -> 21 | Some v -> v) *)

let maximum () = Int.max_int
let minimum () = Int.min_int

let client () =
  assert ((supplied () : int option) = None);
  assert (supplied ~value:7 () = Some 7);
  assert (choose () = 42);
  assert (choose ~value:3 () = 3);
  assert (forward ?value:None () = 42);
  assert (forward ?value:(Some 4) () = 4);
  assert (alias ~value:5 () = 5);
  assert (fallback true ());
  assert (not (fallback true ~value:false ()));
  assert (chained () = (1, 2));
  assert (chained ~first:3 () = (3, 4));
  assert (pair () = (1, 2));
  assert (pair ~pair:(3, 4) () = (3, 4));
  assert (twice () = 42);
  assert (twice ~value:7 () = 14)
