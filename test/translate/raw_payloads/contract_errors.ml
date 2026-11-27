let inspect value = not value
let producer () : bool = Obj.magic ()
let ordinary () = producer ()
let destructure (left, right) = left
