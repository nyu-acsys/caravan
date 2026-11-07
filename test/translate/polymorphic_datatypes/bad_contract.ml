type 'a box = Box of 'a

let select (left : 'a box) (right : 'a box) =
  let (Box _) = left in
  right
(*@ result = select left right ensures result === left *)
