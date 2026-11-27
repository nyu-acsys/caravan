module type ELEMENT = sig
  type t
end

module Make (Element : ELEMENT) = struct
  let keep (value : Element.t) = value
end
