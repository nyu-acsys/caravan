module Static = struct
  let touch () = ()
  (*@ touch () ensures true *)
end

module type VALUE = sig
  type t
end

module Integer = struct
  type t = int
end

module Make (P : VALUE) = struct
  type 'a marker = Marker of 'a

  let touch () = ()
  (*@ touch () ensures true *)
end

module First = Make (Integer)
module Second = Make (Integer)
module Alias = First

let client () =
  Static.touch ();
  Alias.touch ();
  Second.touch ()
