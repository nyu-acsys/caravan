module type Element = sig
  type t
end

module Make (X : Element) = struct
  let good (value : X.t) = value
  (*@ result = good value ensures result === value *)

  let bad () = assert false
end
