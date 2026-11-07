module Stdlib = struct
  module Domain = struct
    type 'a t = Value of 'a
  end
end

let work () = 1
(*@ result = work () ensures result === 1 *)
