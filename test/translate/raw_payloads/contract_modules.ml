module type Transport = sig
  val forward : 'a -> 'a
  (*@ (result [@raw]) = forward (value [@raw])
      ensures Ghost.raw result === Ghost.raw value *)
end

module Native = struct
  let forward value = value
end

module Make (T : Transport) = struct
  let forward value = T.forward value
end

module First = Make (Native)
module Alias = First

let dummy () : bool = Alias.forward (Obj.magic ())
