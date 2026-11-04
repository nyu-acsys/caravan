module type Input = sig end

module Make (Input : Input) = struct
  module Checked : Editor_contract_api.Identity = struct
    let increase actual = actual + 1
  end
end

module Empty = struct end
module First = Make (Empty)
module Second = Make (Empty)
