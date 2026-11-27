type raw = { mutable payload : bool [@caravan.relaxed] [@caravan.raw] }

let ordinary flag =
  let selected = if flag then 1 else 2 in
  let from_match = match flag with true -> Some selected | false -> None in
  (selected, from_match)
