module type Normal = sig
  type t = { mutable value : int [@caravan.relaxed] }
end

module Raw : Normal = struct
  type t = { mutable value : int [@caravan.relaxed] [@caravan.raw] }
end
