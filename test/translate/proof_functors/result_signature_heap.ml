module type ELEMENT = sig
  type t
end

module Make (Element : ELEMENT) : sig
  type t = { value : Element.t array Atomic.t }

  (*@ invariant stored (cell : t) *)

  val keep : t -> t
  (*@ result = keep cell
      requires stored cell
      ensures stored result && result === cell *)
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

let use (cell : Instance.t) = Again.keep cell
