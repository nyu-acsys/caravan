module type VIEW = sig
  type t
end

module Counter = struct
  type t = int

  let identity (value : t) = value
  (*@ result = identity value ensures result = value *)
end

module Make (Cell : VIEW) () = struct
  let identity (value : Cell.t) = value
  (*@ result = identity value ensures result === value *)
end
