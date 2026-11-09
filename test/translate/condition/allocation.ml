module Native = Condition

type condition = Native.t

let make () = Condition.create ()
let alias () : condition = Native.create ()
let same (left : Condition.t) (right : Condition.t) = left == right
let different (left : Condition.t) (right : Condition.t) = left != right

module Condition = struct
  let create () = 7
end

let shadow () = Condition.create ()
