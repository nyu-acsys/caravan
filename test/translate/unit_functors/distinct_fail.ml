module Make () = struct
  type t = Value of int
end

module Make_alias = Make
module First = Make ()
module Second = Make_alias ()

let incorrect (x : First.t) : Second.t = x
