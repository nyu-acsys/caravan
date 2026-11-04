module Box : sig
  val increase : int -> int
  (*@ result = increase specified ensures result = specified + 1 *)
end
