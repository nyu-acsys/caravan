module Checked : Contract_api.Identity = struct
  let identity value = value
end

let client value = Checked.identity value
(*@ result = client value ensures result = value *)
