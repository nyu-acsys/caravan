module type VIEW = sig
  (*@ module R : ResourceAlgebra *)
  (*@ predicate token (cell : Ghost.t) (value : R.t) *)

  val keep : unit -> unit
  (*@ keep () requires token cell value ensures token cell value *)
end

module A = struct
  let keep () = ()
  (*@ keep () requires token cell value ensures token cell value *)
end

module B = struct
  let keep () = ()
  (*@ keep () requires token cell value ensures token cell value *)
end

module Make (X : VIEW) = struct
  let marker (value : int) = value
  (*@ result = marker value
      requires X.token cell X.R.id
      ensures X.token cell X.R.id && result = value *)
end

module One = Make (A)
module Two = Make (B)
