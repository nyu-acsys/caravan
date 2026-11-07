module World : sig
  val use : int -> int
  (*@ result = use value ensures result = value *)
end = struct
  module Inner : sig
    val use : int -> int
    (*@ result = use value ensures result = value *)
  end = struct
    module Helper = struct
      let identity (value : int) = value
      (*@ result = identity value ensures result = value *)
    end

    module Alias = Helper

    let use (value : int) = Alias.identity value
  end

  let use (value : int) = Inner.use value
end

let client (value : int) = World.use value
(*@ result = client value ensures result = value *)
