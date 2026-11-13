val forward : 'a -> 'a

(*@ (result [@raw]) = forward (value [@raw])
    ensures Ghost.raw result === Ghost.raw value *)
val unit_forward : unit -> unit
(*@ (result [@raw]) = unit_forward (value [@raw])
    ensures Ghost.raw result === Ghost.raw value *)
