module Atomic_stack : sig
  type 'a t

  (*@ predicate is_stack (self : 'a t) (share : Permission.t)
      (mutex [@implicit] : Mutex.t) (condition [@implicit] : Condition.t) *)
  (*@ predicate contents (self : 'a t) (values [@implicit] : 'a list) *)
  val make : unit -> 'a t

  (*@ result, [mutex : Mutex.t], [condition : Condition.t] = make () requires Ghost.Mutex.context owner held
      ensures is_stack result Permission.full mutex condition && not (Finset.mem mutex held) &&
        contents result [] *)
  val push : 'a t -> 'a -> unit

  (*@ result = atomic push [mutex : Mutex.t] [condition : Condition.t] r v
      requires is_stack r share mutex condition && Ghost.Mutex.context owner held &&
        not (Finset.mem mutex held)
      ensures is_stack r share mutex condition
      atomic requires contents r values
      atomic ensures contents r (v :: values) *)
  val pop : 'a t -> 'a
  (*@ result = atomic pop [mutex : Mutex.t] [condition : Condition.t] r
      requires is_stack r share mutex condition && Ghost.Mutex.context owner held &&
        not (Finset.mem mutex held)
      ensures is_stack r share mutex condition
      atomic requires contents r values
      atomic ensures match values with
        | [] -> false
        | head :: tail -> contents r tail && result === head *)
end
