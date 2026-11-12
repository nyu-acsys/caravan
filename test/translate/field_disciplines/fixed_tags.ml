module Known = struct
  type t = { mutable counter : int [@caravan.frozen] }
end

module type Input = sig
  type t = Known.t = { mutable counter : int }
end

module Make (X : Input) = struct
  let id (value : int) = value
end

module Result = Make (Known)
