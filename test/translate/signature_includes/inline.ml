module type Signature = sig
  include sig
    val first : int -> int
    (*@ result = first value ensures result = 1 *)
  end

  val second : int -> int
  (*@ result = second value ensures result = 2 *)
end

module Implementation : Signature = struct
  let first (_value : int) = 1
  let second (_value : int) = 2
end

let client value = Implementation.second (Implementation.first value)
(*@ result = client value ensures result = 2 *)
