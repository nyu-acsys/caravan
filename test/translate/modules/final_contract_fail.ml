module Outer = struct
  module Inner = struct
    let identity (value : int) = value
    (*@ result = identity value ensures result <> value *)
  end
end
