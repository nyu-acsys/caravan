module type INPUT = sig
  type t
  (*@ predicate related (value : t) (expected [@implicit] : t) *)

  val identity : t -> t
  (*@ result = identity value ensures result === value *)
end

module A = Values.First
module B = Values.Second

module Make (X : INPUT) = struct
  let read (value : X.t) = X.identity value
  (*@ Ghost.scope (fun step ->
      let token = Read.bind () in
      let result = step () in
      let expected = Read.access token value in
      assert (result === expected);
      Read.commit token value result;
      result) *)
  (*@ manual *)
  (*@ result = atomic read value
      atomic requires X.related value expected && value === expected
      atomic ensures X.related value expected && result === expected *)
end

module One = Make (A)
module Two = Make (B)

let use_one (value : A.t) = One.read value
(*@ result = use_one value
    requires A.related value expected && value === expected
    ensures A.related value expected && result === value *)

let use_two (value : B.t) = Two.read value
(*@ result = use_two value
    requires B.related value expected && value === expected
    ensures B.related value expected && result === value *)
