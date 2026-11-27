type fields = {
  mutable frozen : int; [@caravan.frozen]
  mutable relaxed : bool; [@caravan.relaxed]
}

exception Negative

let helper (value : int) = value
let caller value = helper value
let checked value = if value < 0 then raise Negative else helper value
let caught value = try checked value with Negative -> 0

let repeat count =
  for index = 0 to count do
    (*@ invariant true *)
    let _ = helper index in
    ()
  done

module type SOURCE = sig
  val get : int -> int
  (*@ result = get value
      ensures result = value *)
end

module Make (Source : SOURCE) = struct
  let call value = Source.get value
  (*@ result = call value
      ensures result = value *)
end

module Identity = struct
  let get (value : int) = value
  (*@ result = get value
      ensures result = value *)
end

module Applied = Make (Identity)

let generic_call value = Applied.call value
