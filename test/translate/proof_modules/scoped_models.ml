module Outer = struct
  type t = int

  module Base = struct
    type t = int
  end

  module Left = struct
    type t = int
  end

  module Right = struct
    type t = int
  end

  module Inherited = struct
    module Deep = struct end
  end

  module Later = struct end
  module Alias = Left
end

module A_B = struct
  type t = int
end

module A = struct
  module B = struct
    type t = int
  end
end
