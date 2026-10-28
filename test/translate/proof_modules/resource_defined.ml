module Checked : sig
  type t

  (*@ predicate zero (x : t) = true *)
end = struct
  type t = int Atomic.t
end
