let outer value =
  let helper item = (value, item) in
  helper true
