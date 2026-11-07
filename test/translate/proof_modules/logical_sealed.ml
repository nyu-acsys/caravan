module Outer : sig
  module A : sig end
  module B : sig end
end = struct
  module A = struct end
  module B = struct end
end
