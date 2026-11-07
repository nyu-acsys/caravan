module type Base = sig
  (*@ module R : ResourceAlgebra *)
end

module type Extended = sig
  include Base
end
