type fields = {
  mutable frozen : int; [@caravan.frozen]
  mutable relaxed : bool; [@caravan.relaxed]
}

exception Negative

val helper : int -> int
(*@ result = helper value
    ensures result = value *)

val caller : int -> int
(*@ result = caller value
    ensures result = value *)

val checked : int -> int
(*@ result = checked value
    ensures result = value && value >= 0
    raises Negative -> value < 0 *)

val caught : int -> int
(*@ result = caught value
    ensures result = (if value < 0 then 0 else value) *)

val generic_call : int -> int
(*@ result = generic_call value
    ensures result = value *)

val repeat : int -> unit
(*@ repeat count *)
