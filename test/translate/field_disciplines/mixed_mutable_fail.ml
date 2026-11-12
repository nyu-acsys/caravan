type cell = {
  label : int;
  mutable ordinary : int;
  mutable frozen : int; [@caravan.frozen]
}

let read cell = cell.ordinary
