module Original = struct
  type t = Item of int

  let make value = Item value
  (*@ result = make value ensures result = Item value *)

  let read (item : t) = match item with Item value -> value
  (*@ result = read item ensures match item with Item value -> result = value *)
end

module Alias = Original

module Nested = struct
  module Alias = Alias

  let round_trip value = Alias.read (Original.make value)
  (*@ result = round_trip value ensures result = value *)
end

module Shadow = struct
  module Alias = struct
    let read (value : bool) = not value
    (*@ result = read value ensures result = not value *)
  end
end

let original value = Nested.round_trip value
(*@ result = original value ensures result = value *)

let shadowed value = Shadow.Alias.read value
(*@ result = shadowed value ensures result = not value *)
