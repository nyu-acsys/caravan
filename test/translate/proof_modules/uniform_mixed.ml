module type INPUT = sig
  (*@ predicate ready (value : int) *)
end

module A = struct end

module Unit_first () (X : INPUT) = struct
  let marker (value : int) = value
  (*@ result = marker value requires X.ready value
      ensures X.ready value && result = value *)
end

module Named_first (X : INPUT) () = struct
  let marker (value : int) = value
  (*@ result = marker value requires X.ready value
      ensures X.ready value && result = value *)
end

module U = Unit_first ()
module V = Named_first (A)
module Left = U (A)
module Right = V ()
module Left_alias = Left
module Right_alias = Right
module Left_repeat = U (A)
module U_alias = U
module Left_via_alias = U_alias (A)
module Fresh = Unit_first ()
module Other = Fresh (A)
module Direct = Unit_first () (A)
