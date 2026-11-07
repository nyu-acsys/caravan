module Make () : sig
  type 'a container = { cell : 'a Atomic.t }

  val both : 'a container -> 'a option * 'a * unit
  (*@ result = both q
      requires own q.cell expected
      ensures own q.cell expected && result === (Some expected, expected, ()) *)
end = struct
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
end

module First = Make ()
module Second = Make ()

let client (left : int First.container) (right : bool Second.container) =
  (First.both left, Second.both right)
