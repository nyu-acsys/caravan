module type ELEMENT = sig
  type t
end

module Make (Element : ELEMENT) : sig
  type t = { value : Element.t array Atomic.t }

  (*@ invariant stored (cell : t) (original [@implicit] : t) *)

  val keep : t -> t
  (*@ result = keep cell
      requires stored cell original
      ensures stored result original && result === cell *)
end = struct
  type t = { value : Element.t array Atomic.t }

  let keep (cell : t) =
    let _ = cell.value in
    cell
end

module Integer = struct
  type t = int
end

module Instance = Make (Integer)
module Again = Make (Integer)

module Native = struct
  type t = { value : int }

  let keep (cell : t) = cell
  (*@ result = keep cell requires stored cell
      ensures stored result && result === cell *)

  let fresh (cell : t) = cell
end

module Container = struct
  module Key = struct
    type t = { number : int }
  end

  module Inner = struct
    type t = Key.t

    let keep (cell : t) = cell
    (*@ result = keep cell requires stored cell key
        ensures stored result key && result === cell *)
  end
end

let use (cell : Instance.t) = Again.keep cell
