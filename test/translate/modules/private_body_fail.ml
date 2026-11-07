module Hidden : sig
  val public : int -> int
end = struct
  let public (value : int) = value
  let private_helper (value : int) = value
  (*@ result = private_helper value ensures result <> value *)
end
