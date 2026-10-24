type node = End | Next of int * node Atomic.t

let build values =
  let terminal = Atomic.make End in
  let rec build_next = function
    | [] -> terminal
    | value :: tail -> Atomic.make @@ Next (value, build_next tail)
    (*@ proof fold chain result terminal xs *)
    (*@ result = build_next xs
        requires own terminal End
        ensures own terminal End && chain result terminal xs *)
  in
  (build_next values, terminal)
(*@ manual *)
(*@ result = build values
    ensures match result with (first, limit) ->
      own limit End && chain first limit values *)

let build_with_match values =
  let terminal = Atomic.make End in
  let rec build_explicit xs =
    match xs with
    | [] -> terminal
    | value :: tail -> Atomic.make @@ Next (value, build_explicit tail)
    (*@ proof fold chain result terminal xs *)
    (*@ result = build_explicit xs
        requires own terminal End
        ensures own terminal End && chain result terminal xs *)
  in
  (build_explicit values, terminal)
(*@ manual *)
(*@ result = build_with_match values
    ensures match result with (first, limit) ->
      own limit End && chain first limit values *)

let first_or (fallback : int) = function [] -> fallback | value :: _ -> value
(*@ result = first_or fallback xs ensures selected fallback xs result *)

let aliases (actual : int) = actual
(*@ proof assert (actual = specified) *)
(*@ manual *)
(*@ result = aliases specified ensures result = specified *)

let shadow_alias (actual : int) =
  let specified = 0 in
  actual
(*@ proof assert (specified = 0) *)
(*@ manual *)
(*@ result = shadow_alias specified ensures result = specified *)

let source_names_win (x : int) (y : int) = x
(*@ proof assert (result = x) *)
(*@ manual *)
(*@ result = source_names_win y x ensures result = y *)
