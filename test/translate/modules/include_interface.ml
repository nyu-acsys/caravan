module Impl = struct
  let succ (x : int) = if x < 100 then x + 1 else x
end

include Impl
