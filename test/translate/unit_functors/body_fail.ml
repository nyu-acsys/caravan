module Make () = struct
  type t = Value of int

  let incorrect (x : t) = x
  (*@ result = incorrect x ensures result = Value 0 *)
end

module Instance = Make ()
