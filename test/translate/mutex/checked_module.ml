module Original = struct
  let identity (value : int) = value
  (*@ result = identity value ensures result === value *)
end

module Counter : sig
  val identity : int -> int
  (*@ result = identity value ensures result === value *)
end =
  Original

let client () = Counter.identity 0
