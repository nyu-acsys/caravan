module type Argument = sig end

module A = struct end
module B = struct end

module Make (X : Argument) (Y : Argument) = struct
  type t = Value of int

  let incorrect (x : t) = x
  (*@ result = incorrect x ensures false *)
end

module Instance = Make (A) (B)
