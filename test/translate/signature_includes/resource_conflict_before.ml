module type Base = sig
  (*@ predicate owned (n : int) *)
end

module type Extended = sig
  (*@ predicate owned (n : int) *)
  include Base
end
