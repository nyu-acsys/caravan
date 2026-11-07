module type Element = sig
  type t
end

module Worker (A : Element) (B : Element) () = struct
  let work (left : A.t) (right : B.t) = (left, right)
  (*@ result = work left right ensures result === (left, right) *)

  let run left right =
    let domain = Domain.spawn (fun () -> work left right) in
    Domain.join domain
  (*@ result = run left right ensures result === (left, right) *)
end

module Int = struct
  type t = int
end

module Bool = struct
  type t = bool
end

module Partial = Worker (Int)
module First = Partial (Bool) ()
module Second = Worker (Int) (Bool) ()

let client () = First.run 7 true
(*@ result = client () ensures result === (7, true) *)
