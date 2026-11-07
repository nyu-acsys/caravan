module type INPUT = sig
  (*@ predicate ready (value : int) *)
end

module Static = struct
  let identity (value : int) = value
  (*@ result = identity value ensures result = value *)
end

module Static_alias = Static
module A = struct end

module Make (X : INPUT) = struct
  let read (value : int) = Static.identity value
  (*@ result = read value requires X.ready value
      ensures X.ready value && result = value *)
end

module Unit () = struct
  let read (value : int) = Static_alias.identity value
  (*@ result = read value ensures result = value *)
end

module Curried (X : INPUT) () = struct
  let read (value : int) = Static.identity value
  (*@ result = read value requires X.ready value
      ensures X.ready value && result = value *)
end

module Named = Make (A)
module Fresh = Unit ()
module Partial = Curried (A)
module Applied = Partial ()

let client (value : int) = Applied.read (Fresh.read (Named.read value))
(*@ result = client value requires A.ready value
    ensures A.ready value && result = value *)
