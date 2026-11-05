module type Original = sig
  val identity : int -> int
  (*@ result = identity value ensures result = value *)
end

module type Included = sig
  include Original
end

module Implementation : Included = struct
  let identity (_value : int) = 0
end
