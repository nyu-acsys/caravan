let equal (left : Mutex.t) (right : Mutex.t) = left == right
(*@ result = equal left right ensures result = (left = right) *)
