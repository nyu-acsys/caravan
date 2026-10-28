module Left = struct
  type t = int

  let identity (x : t) = x
  (*@ result = identity x ensures result = shift x *)
end

module Right = struct
  type t = int

  let identity (x : t) = x
  (*@ result = identity x ensures result = shift x *)
end

module Alias = Left

let client x = Alias.identity x
(*@ result = client x ensures result = Alias.shift x *)
