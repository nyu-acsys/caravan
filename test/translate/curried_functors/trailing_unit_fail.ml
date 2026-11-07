module type Argument = sig end

module A = struct end

module Fresh (X : Argument) () = struct
  type t = { contents : int }
end

module With_A = Fresh (A)
module With_A_alias = With_A
module First = With_A ()
module Second = With_A_alias ()

let incorrect (x : First.t) : Second.t = x
