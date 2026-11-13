module Alias = Raw_helpers

let forward value = Alias.forward value
let dummy () : bool = forward (Obj.magic ())

let unit_dummy () =
  let _ = Alias.unit_forward (Obj.magic ()) in
  ()
