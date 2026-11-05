type _ kind = Integer : int kind | Boolean : bool kind

let read_as : type r. r kind -> r =
 fun kind ->
  let cell = Atomic.make () in
  let () = Atomic.get cell in
  match kind with Integer -> 17 | Boolean -> true

let integer () = read_as Integer
let boolean () = read_as Boolean
