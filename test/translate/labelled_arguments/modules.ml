module type Select = sig
  val choose : left:'a -> right:'a -> 'a
  (*@ result = choose left right ensures result === left *)
end

module Native = struct
  let choose ~left ~right:_ = left
end

module Make (Select : Select) = struct
  let choose ~left ~right = Select.choose ~right ~left
end

module Instance = Make (Native)
module Alias = Instance

let client () =
  assert (Alias.choose ~right:2 ~left:1 = 1);
  assert (Alias.choose ~left:true ~right:false)
