module type STACK = sig
  type 'a t

  (*@ predicate stack (st : 'a t) (items [@implicit] : 'a list) *)
end

module Make (Stack : STACK) = struct
  let preserve (st : int Stack.t) = ()
  (*@ preserve st requires running st ensures running st *)
end
