module Work = struct
  let succeeds () = assert (1 = 1)
  let fails () = assert false
end

module Make () = struct
  let identity (value : int) = value
  (*@ result = identity value ensures result = value *)
end

module Made = Make ()
