module Checked = struct
  type t = { mutable count : int }

  let make () = { count = 0 }
end
