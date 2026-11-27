type fields = { mutable counter : int [@caravan.frozen] }

val id : int -> int
(*@ result = id value
    ensures result = value *)
