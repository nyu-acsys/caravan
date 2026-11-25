module type ORDINARY = sig
  type t

  val hash : t -> int
  (*@ result = hash key ensures 0 <= result *)
end

module type PURE = sig
  type t

  val hash : t -> int
  (*@ result = hash key pure ensures 0 <= result *)
end

module Make (Key : PURE) = struct
  let hash key = Key.hash key
end

module Forward (Key : ORDINARY) = struct
  module Invalid = Make (Key)
end
