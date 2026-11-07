module Make () = struct
  let identity (x : int) = x
end

module Client = Make ()
