val identity : int -> int [@@caravan.local]
(*@ result = identity value
    ensures result = value *)
