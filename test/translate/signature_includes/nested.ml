module type Original = sig
  type t

  val identity : t -> t
  (*@ result = identity value ensures result = value *)
end

module type Nested = sig
  module Member : sig
    include Original
  end
end

module type Repeated = sig
  include Nested
end

module Implementation : Repeated = struct
  module Member = struct
    type t = int

    let identity value = value
  end
end

let client (value : Implementation.Member.t) = Implementation.Member.identity value
(*@ result = client value ensures result = value *)
