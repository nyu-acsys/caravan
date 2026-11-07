module Left = struct
  module Inner = struct
    type t = Box of int

    let make value = Box value
    (*@ result = make value ensures result = Box value *)

    let measure (_value : t) = 0
  end
end

module Right = struct
  module Inner = struct
    type t = Box of bool

    let make value = Box value
    (*@ result = make value ensures result = Box value *)

    let measure (_value : t) = 1
  end
end

let integer_box value = Left.Inner.make value
(*@ result = integer_box value ensures result = Left.Inner.Box value *)

let boolean_box value = Right.Inner.make value
(*@ result = boolean_box value ensures result = Right.Inner.Box value *)

let combined (left : Left.Inner.t) (right : Right.Inner.t) =
  Left.Inner.measure left + Right.Inner.measure right
(*@ result = combined left right
    ensures result = 1 && Left.Inner.measure left = 0 && Right.Inner.measure right = 1 *)
