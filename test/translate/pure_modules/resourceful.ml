module type KEY = sig
  type t

  (*@ predicate owned (key : t) *)
  val hash : t -> int
  (*@ result = hash x pure requires owned x ensures 0 <= result *)
end

module Make (Key : KEY) = struct
  let hash x = Key.hash x
end
