module Checked : Contract_api.Identity = struct
  let identity (value : int) = if value = 0 then 1 else value
end
