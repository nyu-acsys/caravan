module Hidden : sig
  val public : int -> int
end = struct
  let private_helper (value : int) = value
  let public value = private_helper value
end

let call value = Hidden.private_helper value
