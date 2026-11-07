let outer value =
  let helper () = value in
  (*@ result = helper () ensures result === 0 *)
  helper ()
