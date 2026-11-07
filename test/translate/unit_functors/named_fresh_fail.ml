module Factory () = struct
  type t = Value of int
end

module type Argument = sig end

module Make (X : Argument) = struct
  module Instance = Factory ()
end

module Actual = struct end
module Instance = Make (Actual)
