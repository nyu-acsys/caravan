module type Argument = sig end

module Make (X : Argument) () (Y : Argument) = struct
  let incorrect () = assert false
end
