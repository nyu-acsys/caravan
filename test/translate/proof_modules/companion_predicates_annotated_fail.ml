module Box : sig
  type t
  (*@ predicate visible (value : t) *)
end = struct
  type t = int
end

let client (value : Box.t) = ()
