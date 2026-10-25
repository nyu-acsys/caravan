module Sealed : sig
  type t = private Hidden

  val make : unit -> t
  (*@ result = make () ensures result = Hidden *)
end = struct
  type t = Hidden

  let make () = Hidden
end
