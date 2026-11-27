module Stdlib = struct
  module Obj = struct
    let magic () = true
  end
end

let normal () = Stdlib.Obj.magic ()
