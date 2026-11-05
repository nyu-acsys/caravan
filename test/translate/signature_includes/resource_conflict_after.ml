module type Base = sig
  (*@ predicate owned (n : int) *)
end

module type Extended = sig
  include Base

  (*@ predicate owned (n : int) *)
end
