let identity value = value
(*@ result = identity value pure ensures result === value *)

module Make () = struct
  let identity_int (value : int) = value
  (*@ result = identity_int value pure ensures result === value *)
end

module Instance = Make ()

let checked_identity value =
  (*@ lemma reflex value *)
  value
(*@ result = checked_identity value ensures result === value *)

let integer () = checked_identity 17
(*@ result = integer () ensures result === 17 *)

let boolean () = checked_identity true
(*@ result = boolean () ensures result *)
