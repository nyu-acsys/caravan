module type Argument = sig end

module A = struct end
module Make (X : Argument) (Y : Argument) = struct end
module Partial = Make (A)
module Instance = Partial (struct end)
