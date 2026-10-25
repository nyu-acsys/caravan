module type STACK = sig
  type t

  (*@ predicate stack (t : t) (xs : int list) *)
  val pop_opt : t -> int option
  (*@ result = atomic pop_opt t
      atomic requires stack t xs
      atomic ensures match xs with
        | [] -> result = None && stack t []
        | x :: xs' -> result = Some x && stack t xs' *)
end

module Test (Stack : STACK) = struct
  let rec drain stack =
    match Stack.pop_opt stack with None -> [] | Some value -> value :: drain stack
  (*@ result = drain stack
      requires Stack.stack stack xs
      ensures Stack.stack stack [] && result = [] *)
end

module Client = Test (Treiber_stack)
