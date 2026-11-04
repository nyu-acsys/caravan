val increase : int -> int
(*@ result = increase specified
    requires (* 🙂 *) specified >= 0
    ensures result = specified + 1
    variant specified *)

val inline : int -> int

module Box : sig
  val increase : int -> int
  (*@ result = increase specified ensures result = specified + 1 *)
end

val atomic_identity : int -> int
(*@ result = atomic atomic_identity specified
    atomic requires specified >= 0
    atomic ensures result = specified
    atomic raises Not_found -> false *)

val pure_identity : int -> int
(*@ result = pure_identity specified pure ensures result = specified *)

val exceptional : int -> int
(*@ result = exceptional specified
    raises Failure message -> message = "🙂"
    raises Not_found
    ensures result = specified *)
