module Box : sig
  type t
end = struct
  type t = int
end

let client (value : Box.t) = ()
