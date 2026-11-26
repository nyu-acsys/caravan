module Opened = struct
  open struct
    let identity (value : int) = value
  end

  let call value = identity value
end
