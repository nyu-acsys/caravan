(** Distinct names, as Raven needs them: a base, or the base with the first index that
    makes it unused. The program's modules, types and functions share one namespace, whose
    names come from the supply here. *)

open Base

(** A name for [base] not in [used]. *)
let unused used base =
  let rec go n =
    let candidate = if n = 0 then base else Printf.sprintf "%s_%d" base n in
    if Set.mem used candidate then go (n + 1) else candidate
  in
  go 0

let given = ref (Set.empty (module String))

(** Starts a new program, with no names given. *)
let reset () = given := Set.empty (module String)

(** Keeps [names] from being given. *)
let reserve names = given := Set.union !given (Set.of_list (module String) names)

(** A name of the program for [base], not given or reserved yet. *)
let fresh base =
  let name = unused !given base in
  given := Set.add !given name;
  name
