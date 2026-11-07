module Original = struct
  let identity (value : int) = value
end

module Checked : Contract_api.Identity = Original
