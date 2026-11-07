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
let keyed = ref (Map.empty (module String))

(** Starts a new program, with no names given. *)
let reset () =
  given := Set.empty (module String);
  keyed := Map.empty (module String)

type snapshot = Set.M(String).t * string Map.M(String).t

(** The names given so far, to [restore] for translating the program again. *)
let save () : snapshot = (!given, !keyed)

let restore ((names, keys) : snapshot) =
  given := names;
  keyed := keys

(** Keeps [names] from being given. *)
let reserve names = given := Set.union !given (Set.of_list (module String) names)

(** A name of the program for [base], not given or reserved yet. *)
let fresh base =
  let name = unused !given base in
  given := Set.add !given name;
  name

(** Structural keys can embed earlier generated names, so retaining their complete text in
    names would grow recursively. The digest bounds names and makes them independent of
    request order; collisions abort rather than identify different declarations. *)
let for_key ~key base =
  match Map.find !keyed key with
  | Some name -> name
  | None ->
      let name = base ^ "$" ^ Stdlib.Digest.(to_hex (string key)) in
      if Set.mem !given name then
        failwith ("A generated structural name collides: " ^ name);
      given := Set.add !given name;
      keyed := Map.set !keyed ~key ~data:name;
      name
