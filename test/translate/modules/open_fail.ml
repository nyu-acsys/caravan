module Original = struct
  let identity (value : int) = value
end

module Opened = struct
  open Original

  let call value = identity value
end
