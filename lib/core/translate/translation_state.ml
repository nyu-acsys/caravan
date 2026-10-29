(** The state of a translation, threaded explicitly: what each arm of a branch starts
    from, what carries on from arm to arm within a procedure, the supply of fresh names,
    the fields and primitives used, and the checks generated. *)

open Base
open Translate_context

type au_path = {
  au_state : au_state;
  au_step : Location.t;
  au_values : R.Expr.t list;
  au_performing : (performing * R.Expr.t option) option;
}
(** The part of an atomic update that each arm of a branch starts from. *)

type path = {
  opened : (string * opened) list;
  snapshots : (string * opened list) list;
  positions : position list;
  au : au_path option;
}
(** What each arm of a branch starts from. *)

type carried = {
  ghost_returns : (string * string * Types.type_expr) list;
  proof_state : (R.Expr.t * Types.type_expr) option;
  return_covered : bool;
  fields_of : (string * (string * R.Expr.t)) list;
  formals : R.Expr.t list;
  facts : R.Spec.t list;
  invariants : (string * R.Expr.t list) list;
  au_results : ((string * bool) list * string list) option;
      (** The variables bound to the results of an atomic update's [compare_and_set]s and
          reads. *)
}
(** What carries on from arm to arm within a procedure. *)

type names = {
  used : Set.M(String).t;
  bound : (string * string) list;
  scope : (string * (string * Types.type_expr option)) list;
}

type tables = { cells : cell_field list; primitives : (string * R.Member.t) list }

type state = {
  path : path;
  carried : carried;
  names : names;
  tables : tables;
  origins : origin list;  (** The checks generated so far, latest first. *)
}

type 'a t = state -> ('a, error) Result.t * state
(** A computation on the state: its result, and its state at the end, which on an error is
    the state when it failed, as with mutable state. *)

let return a s = (Ok a, s)
let fail e s = (Error e, s)
let bind m ~f s = match m s with Ok a, s -> f a s | (Error _ as error), s -> (error, s)

let map m ~f s =
  let r, s = m s in
  (Result.map r ~f, s)

let of_result r s = (r, s)

(** [m]'s result as a value, an error included, with the state it ends in. *)
let attempt m s =
  let r, s = m s in
  (Ok r, s)

let get s = (Ok s, s)
let put s _ = (Ok (), s)
let modify f s = (Ok (), f s)
let gets f s = (Ok (f s), s)

module Syntax = struct
  let ( let* ) m f = bind m ~f
  let ( let+ ) m f = map m ~f
end

(** Runs each of [arms] from the path before them, the rest of the state carrying on from
    arm to arm: their results with the path each ends in. The path is then the last arm's.
*)
let arms (arms : 'a t list) : ('a * path) list t =
 fun s ->
  let start = s.path in
  let rec go s ended = function
    | [] -> (Ok (List.rev ended), s)
    | arm :: rest ->
        begin match arm { s with path = start } with
        | Ok a, s -> go s ((a, s.path) :: ended) rest
        | (Error _ as error), s -> (error, s)
        end
  in
  go s [] arms

(** The state that [ctx] holds. *)
let capture (ctx : context) : state =
  let p = ctx.procedure in
  {
    path =
      {
        opened = p.opened;
        snapshots = p.snapshots;
        positions = p.positions;
        au =
          Option.map p.au ~f:(fun au ->
              {
                au_state = au.state;
                au_step = au.step;
                au_values = au.values;
                au_performing = au.performing;
              });
      };
    carried =
      {
        ghost_returns = p.ghost_returns;
        proof_state = p.proof_state;
        return_covered = p.return_covered;
        fields_of = p.fields_of;
        formals = p.formals;
        facts = p.facts;
        invariants = p.invariants;
        au_results = Option.map p.au ~f:(fun au -> (au.cas_results, au.read_results));
      };
    names = { used = p.names.used; bound = p.names.bound; scope = p.names.scope };
    tables = { cells = !(ctx.collected.refs); primitives = !(ctx.collected.primitives) };
    origins = !(ctx.collected.origins);
  }

(** Makes [ctx] hold the state [s]. *)
let restore (ctx : context) (s : state) =
  let p = ctx.procedure in
  p.opened <- s.path.opened;
  p.snapshots <- s.path.snapshots;
  p.positions <- s.path.positions;
  Option.iter p.au ~f:(fun au ->
      Option.iter s.path.au ~f:(fun path ->
          au.state <- path.au_state;
          au.step <- path.au_step;
          au.values <- path.au_values;
          au.performing <- path.au_performing);
      Option.iter s.carried.au_results ~f:(fun (cas_results, read_results) ->
          au.cas_results <- cas_results;
          au.read_results <- read_results));
  p.ghost_returns <- s.carried.ghost_returns;
  p.proof_state <- s.carried.proof_state;
  p.return_covered <- s.carried.return_covered;
  p.fields_of <- s.carried.fields_of;
  p.formals <- s.carried.formals;
  p.facts <- s.carried.facts;
  p.invariants <- s.carried.invariants;
  p.names.used <- s.names.used;
  p.names.bound <- s.names.bound;
  p.names.scope <- s.names.scope;
  ctx.collected.refs := s.tables.cells;
  ctx.collected.primitives := s.tables.primitives;
  ctx.collected.origins := s.origins

(** Runs [m] on the state that [ctx] holds, which then holds the state [m] ends in. *)
let run (ctx : context) (m : 'a t) : ('a, error) Result.t =
  let r, s = m (capture ctx) in
  restore ctx s;
  r
