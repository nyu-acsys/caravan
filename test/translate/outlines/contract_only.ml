let identity (value : int) = value

let twice value =
  let helper (item : int) = item in
  helper (helper value)
