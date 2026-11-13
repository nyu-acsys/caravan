let required ?(token = ()) (Some value) =
  let _ = token in
  value

let defaulted ?value:(Some item = Some 42) () = item
