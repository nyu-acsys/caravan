module Counter : sig
  type t
end = struct
  type t = int
end

module Outside = struct end
