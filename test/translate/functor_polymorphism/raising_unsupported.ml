exception E

module type S = sig
  val run : 'a -> unit
  (*@ run value ensures true *)
end

module Bad = struct
  let run value : unit = raise E
  (*@ run value raises E -> true *)
end

module Apply (Argument : S) = struct
  let call value = Argument.run value
  (*@ call value ensures true *)
end

module Actual = Apply (Bad)

let client () = Actual.call 17
(*@ client () ensures true *)
