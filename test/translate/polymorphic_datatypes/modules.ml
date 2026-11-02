module Boxes = struct
  type 'a t = Box of 'a
  type 'a alias = 'a t

  let keep (value : 'a alias) = value
  (*@ result = keep value pure ensures result === value *)

  type 'a record = { contents : 'a }
  type 'a record_alias = 'a record

  let keep_record (value : 'a record_alias) = value
  (*@ result = keep_record value pure ensures result === value *)
end

module type VALUE = sig
  type t
end

module Integer = struct
  type t = int
end

module Boolean = struct
  type t = bool
end

module Make (P : VALUE) = struct
  type 'a t = Pair of P.t * 'a
  type 'a alias = 'a t
  type 'a envelope = { payload : 'a; numbers : int list }

  let envelope payload = { payload; numbers = [] }
  (*@ result = envelope payload pure ensures result.payload === payload *)

  let pair fixed value = Pair (fixed, value)
  (*@ result = pair fixed value pure ensures result === Pair (fixed, value) *)

  let keep (value : 'a alias) = value
  (*@ result = keep value pure ensures result === value *)
end

module First = Make (Integer)
module Second = Make (Integer)
module Third = Make (Boolean)
module Alias = First

let static_roundtrip (value : int) =
  match Boxes.keep (Boxes.Box value) with Boxes.Box result -> result
(*@ result = static_roundtrip value ensures result === value *)

let record_roundtrip (value : bool) =
  (Boxes.keep_record { Boxes.contents = value }).contents
(*@ result = record_roundtrip value ensures result === value *)

let functor_roundtrip (fixed : int) (value : bool) =
  match Second.keep (Alias.keep (First.Pair (fixed, value))) with
  | Second.Pair (result, flag) -> (result, flag)
(*@ result = functor_roundtrip fixed value ensures result === (fixed, value) *)

let envelope_roundtrip () = (First.envelope true).payload
(*@ result = envelope_roundtrip () ensures result *)

let other_argument () =
  match Third.keep (Third.Pair (true, 17)) with Third.Pair (flag, value) -> (flag, value)
(*@ result = other_argument () ensures result === (true, 17) *)

let construct_other () = Third.pair true 17
(*@ result = construct_other () ensures result === Third.Pair (true, 17) *)
