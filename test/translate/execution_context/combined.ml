type fields = { mutable frozen : int [@caravan.frozen] }

exception Negative

let checked (value : int) = if value < 0 then raise Negative else value
let caught value = try checked value with Negative -> 0

let repeat count =
  for index = 0 to count do
    (*@ invariant Ghost.Mutex.context self held *)
    let _ = caught index in
    ()
  done
