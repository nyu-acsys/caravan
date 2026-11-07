module type STRONG = sig
  (*@ module R : CancellativeResourceAlgebra *)
end

module type WEAK = sig
  module B : sig
    (*@ module R : ResourceAlgebra *)
  end
end

module Outer : WEAK = struct
  module B : STRONG = struct end
end
