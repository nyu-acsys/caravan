module Make () = struct
  type t = Value of int

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module Instance = Make ()

let incorrect () = Instance.identity (Instance.Value 7)
(*@ result = incorrect () ensures result = Instance.Value 8 *)
