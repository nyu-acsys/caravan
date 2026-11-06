module Make () = struct
  let incorrect (x : int) = x
  (*@ result = incorrect x ensures result = x + 1 *)
end
