module type INNER = sig
  (*@ module R : ResourceAlgebra *)
end

module type OUTER = sig
  module B : sig
    (*@ module R : ResourceAlgebra *)
  end
end

module Outer : OUTER = struct
  module B : INNER = struct end
end
