module Open : sig
  type t
  (*@ predicate wrapped (cell : t) (n [@implicit] : int) *)
end

module Sealed : sig
  type t
  (*@ predicate wrapped (cell : t) (n [@implicit] : int) *)
end
