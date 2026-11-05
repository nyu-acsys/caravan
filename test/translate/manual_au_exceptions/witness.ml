type ('a, _) kind = Value : ('a, 'a) kind | Option : ('a, 'a option) kind

let read_as : type a r. a Atomic.t -> (a, r) kind -> r =
 fun cell kind ->
  let value = Atomic.get cell in
  match kind with Value -> value | Option -> Some value

let read_value cell = read_as cell Value
let read_option cell = read_as cell Option
