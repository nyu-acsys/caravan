module Checked : sig
  type t

  (*@ predicate owned (x : t) (n [@implicit] : int) *)
end = struct
  type t = { mutable count : int }
end
