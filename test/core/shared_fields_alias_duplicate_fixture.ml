module Cells = struct
  type t = { mutable count : int [@caravan.frozen] }
end
