module Cells = struct
  type cell = { mutable value : int }
  type holder = { mutable next : cell }
end

module Alias = Cells
