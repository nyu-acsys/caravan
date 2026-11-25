module type ELEMENT = sig
  type t
end

module Make (Element : ELEMENT) = struct
  let bump (counter : int Atomic.t) (value : Element.t) =
    Atomic.incr counter;
    Atomic.decr counter;
    value
end
