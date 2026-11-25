module Box : sig
  val increase : int -> int
  (*@ result = increase specified ensures result = specified + 1 *)
end = struct
  let increase actual = actual + 1
  (*@ result = increase actual ensures result = actual + 1 *)
end
