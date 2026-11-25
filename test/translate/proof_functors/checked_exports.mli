module First : sig
  val keep : int -> int
  (*@ result = keep x ensures result === x *)
end

module Second : sig
  val keep : int -> int
  (*@ result = keep x ensures result === x *)
end

module Native : sig
  val keep : int -> int

  (*@ result = keep x ensures true *)
  val fresh : int -> int
  (*@ result = fresh x ensures result === x *)
end

val client : int -> int
(*@ result = client x ensures result === x *)
