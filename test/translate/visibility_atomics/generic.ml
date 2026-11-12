type unused = { mutable data : int [@caravan.frozen] }

let create value = Atomic.make value
(*@ cell = create value ensures own cell value *)

let get cell = Atomic.get cell
(*@ result = get cell
    requires own cell value
    ensures own cell value && result === value *)

let exchange cell value = Atomic.exchange cell value
(*@ result = exchange cell value
    requires own cell previous
    ensures own cell value && result === previous *)

module type VALUE = sig
  type t
end

module Make (Value : VALUE) = struct
  let create (value : Value.t) = Atomic.make value
  (*@ cell = create value ensures own cell value *)

  let exchange (cell : Value.t Atomic.t) value = Atomic.exchange cell value
  (*@ result = exchange cell value
      requires own cell previous
      ensures own cell value && result === previous *)
end

module IntegerValue = struct
  type t = int
end

module BooleanValue = struct
  type t = bool
end

module Integer = Make (IntegerValue)
module Boolean = Make (BooleanValue)

let client () =
  let integer = create 7 in
  let boolean = create true in
  assert (get integer = 7);
  assert (exchange boolean false);
  let integer = Integer.create 9 in
  assert (Integer.exchange integer 10 = 9);
  let boolean = Boolean.create false in
  assert (not (Boolean.exchange boolean true))
(*@ client () *)
