type cell = {
  mutable frozen : int; [@caravan.frozen]
  mutable relaxed : int; [@caravan.relaxed]
}

let read cell = cell.frozen
let write cell value = cell.frozen <- value
let relaxed_read cell = cell.relaxed
