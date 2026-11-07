module type Argument = sig end

module A = struct end
module B = struct end

module Make (X : Argument) (Y : Argument) = struct
  let identity (x : int) = x
  (*@ result = identity x ensures result = x *)
end

module With_A = Make (A)
module Instance = With_A (B)

let incorrect () = Instance.identity 7
(*@ result = incorrect () ensures result = 8 *)
