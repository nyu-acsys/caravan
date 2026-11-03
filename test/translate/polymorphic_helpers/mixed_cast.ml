let outer value =
  let helper item = value in
  (*@ result = helper item ensures result === item *)
  helper value
