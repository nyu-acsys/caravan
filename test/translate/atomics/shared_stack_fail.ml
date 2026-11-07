(* A shared stack with bugs, against shared_stack_fail.mli and shared_stack_fail.proof. *)

type t = int list Atomic.t

(* The stack starts with an element, but its view says it is empty. *)
let create () = Atomic.make [ 1 ]

(* The value is not pushed, but the view says it is. *)
let rec push t value =
  let before = Atomic.get t in
  if not (Atomic.compare_and_set t before before) then push t value

(* Emptying the stack changes its state, which no view follows. *)
let clear t = Atomic.set t []
