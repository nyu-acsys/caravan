let increase actual = actual + 1
let inline actual = actual
(*@ result = inline actual ensures result = actual *)

module Box = struct
  let increase actual = actual + 1
end

let atomic_identity actual = actual
let pure_identity actual = actual
let exceptional actual = actual
