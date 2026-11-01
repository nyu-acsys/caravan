let first (items : int list) = match items with [] -> 0 | head :: _ -> head
(*@ result = first items pure *)

let invalid () = ()
(*@ invalid () ensures first [4611686018427387903 + 1] <= 4611686018427387903 *)
