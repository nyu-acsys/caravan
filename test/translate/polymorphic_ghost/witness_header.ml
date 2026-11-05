type 'a container = { cell : 'a Atomic.t }

type ('a, _) poly =
  | Option : ('a, 'a option) poly
  | Value : ('a, 'a) poly
  | Unit : ('a, unit) poly

let read_as : type a r. a Atomic.t -> (a, r) poly -> r =
 fun cell poly ->
  let value = Atomic.get cell in
  match poly with Option -> Some value | Value -> value | Unit -> ()

let both q = (read_as q.cell Option, read_as q.cell Value, read_as q.cell Unit)
