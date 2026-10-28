module Nested = struct
  type t = int Atomic.t

  let read (x : t) = Atomic.get x
end
