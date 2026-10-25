module A = struct
  module B = struct
    let f (_value : int) = 0
  end
end

module A_B = struct
  let f (_value : int) = 1
end

let foo (_value : int) = 0
let foo_impl (_value : int) = 1
(*@ result = foo_impl value ensures result = 1 *)

let namespaces value = A.B.f value + A_B.f value
(*@ result = namespaces value
    ensures result = 1 && A.B.f value = 0 && A_B.f value = 1 *)

let procedure value = foo value + foo_impl value
(*@ result = procedure value ensures result = 1 && foo value = 0 *)
