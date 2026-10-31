(** How the histories of states are encoded. *)

type encoding =
  | Sets
      (** The authority over the set of the states that the current one extends, and
          fragments holding sets of states, in Raven's [Library.Auth] over
          [Library.SetRA]. *)
  | Monotone
      (** The authority over the current state, and fragments holding lower bounds of it,
          composed by their join (see {!Monotone_history}). *)

let default = Sets

(** The encodings, by their names on the command line. *)
let encodings = [ ("sets", Sets); ("monotone", Monotone) ]

(** The members that a program with histories defines once. *)
let program_members = function Sets -> [] | Monotone -> Monotone_history.members
