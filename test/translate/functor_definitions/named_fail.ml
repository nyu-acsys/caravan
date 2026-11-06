module type Argument = sig end

module Make (X : Argument) = struct
  let incorrect () = assert false
end
