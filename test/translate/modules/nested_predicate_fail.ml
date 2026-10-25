module Container = struct
  type t = int

  (*@ predicate holds (value : t) *)

  let identity (value : t) = value
end
