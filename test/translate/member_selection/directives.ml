module Scope = struct
  let good () = ()
# 1 "selection_virtual.ml"
  let bad () = assert false
end

let outer () =
# 1 "selection_virtual_nested.ml"
  let helper () = assert false in
  helper ()
