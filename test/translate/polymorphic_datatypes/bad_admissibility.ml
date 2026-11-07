type 'a box = Box of 'a

let extract (box : int box) = match box with Box value -> value
(*@ result = extract box pure
    ensures match box with Box value -> result === value *)

let invalid_bound () = ()
(*@ invalid_bound () ensures extract (Box (max_int + 1)) <= max_int *)
