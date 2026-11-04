module Box = struct
  let increase actual = actual + 1
  (*@ result = increase actual ensures result = actual + 1 *)
end
