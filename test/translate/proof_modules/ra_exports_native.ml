module Native = struct
  type t = int
end

module Opaque : sig
  type t
end = struct
  type t = int
end

let marker (value : Native.t) = value
(*@ result = marker value ensures result = value *)
