module Original = struct
  let identity (value : int) = value
end

module Included = struct
  include Original
end
