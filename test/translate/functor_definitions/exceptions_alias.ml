module Make () = struct
  exception Empty

  let get (x : int) = if x = 0 then raise Empty else x
  (*@ result = get x
      ensures result = x && x <> 0
      raises Empty -> x = 0 *)
end

module First = Make ()
module Second = Make ()
module Alias = First

let get_or_zero (x : int) = try Alias.get x with Second.Empty -> 7 | Alias.Empty -> 0
(*@ result = get_or_zero x ensures result = x *)

module A = struct
  module First = Make ()
  module Alias = First

  let get (x : int) = try Alias.get x with Alias.Empty -> 0
  (*@ result = get x ensures result = x *)
end

module B = struct
  module First = Make ()
  module Alias = First

  let get (x : int) = try Alias.get x with Alias.Empty -> 0
  (*@ result = get x ensures result = x *)
end
