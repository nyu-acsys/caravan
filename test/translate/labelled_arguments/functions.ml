let choose ~left ~right:_ = left
let alias = choose

type 'a box = { item : 'a }

let item ~box:{ item } ~token:() = item
let duplicate ~value = value + value
(*@ result = duplicate value pure
    requires 0 <= value && value <= 100
    ensures result = 2 * value *)

let client () =
  assert (choose ~right:2 ~left:1 = 1);
  assert (alias ~right:false ~left:true);
  assert (item ~token:() ~box:{ item = 42 } = 42);
  assert (duplicate ~value:7 = 14)
