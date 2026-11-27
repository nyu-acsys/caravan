type fields = {
  mutable frozen : int; [@caravan.frozen]
  mutable relaxed : bool; [@caravan.relaxed]
}

let read (record : fields) = record.frozen
