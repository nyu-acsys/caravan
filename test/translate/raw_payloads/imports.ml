module Alias = Raw_cell

let allocate value = { Alias.value }
let read (cell : bool Alias.t) = cell.value
