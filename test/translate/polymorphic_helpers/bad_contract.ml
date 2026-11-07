let outer left right =
  let helper () = if true then right else left in
  (*@ result = helper () ensures result === left *)
  helper ()
