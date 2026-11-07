module Make (Argument : sig
  val value : int
end) =
struct
  let get () = Argument.value
end
