(**************************************************************************)
(*                                                                        *)
(*  GOSPEL -- A Specification Language for OCaml                          *)
(*                                                                        *)
(*  Copyright (c) 2018- The VOCaL Project                                 *)
(*                                                                        *)
(*  This software is free software, distributed under the MIT license     *)
(*  (as described in file LICENSE enclosed).                              *)
(**************************************************************************)

(* Gospel's untyped terms (parse_uast.mli, preid.ml and uast_utils.ml of
   github.com/ocaml-gospel/gospel at ce26d16), for Caravan's contracts: with match,
   constructor patterns and Caravan's contracts. *)

type fixity = Normal | Infix | Mixfix | Prefix

type id = {
  pid_str : string;
  pid_fixity : fixity;
  pid_attrs : string list;
  pid_loc : Location.t;
}

let mk_id ?(fixity = Normal) ?(attrs = []) ~loc str =
  { pid_str = str; pid_fixity = fixity; pid_attrs = attrs; pid_loc = loc }

let add_attr id attr = { id with pid_attrs = attr :: id.pid_attrs }

type qualid = Qid of id | Qdot of qualid * id

let rec qualid_loc = function Qid id -> id.pid_loc | Qdot (_, id) -> id.pid_loc

type pty =
  | PTtyvar of id
  | PTtyapp of qualid * pty list
  | PTtuple of pty list
  | PTarrow of pty * pty

type labelled_arg = Lwild | Lunit of Location.t | Lvar of id | Lghost of id * pty
type binder = id * pty option

type constant =
  | Pconst_integer of string * char option
  | Pconst_char of char
  | Pconst_string of string * Location.t
  | Pconst_float of string

type pat = { pat_desc : pat_desc; pat_loc : Location.t }

and pat_desc =
  | Pwild
  | Pid of id
  | Ptuple of pat list
  | Pcast of pat * pty
  | Pconstr of qualid * pat option  (** [C], or [C p] where [p] may be a tuple. *)
  | Pconst of constant

type quant = Tforall | Texists

type term = { term_desc : term_desc; term_loc : Location.t }

and term_desc =
  | Ttrue
  | Tfalse
  | Tconst of constant
  | Tvar of qualid
  | Tfield of term * qualid
  | Tapply of term * term
  | Tinfix of term * id * term
      (** A chain of infix operations, as [e1 < e2 < e3], until [chain] desugars it. *)
  | Tif of term * term * term
  | Tquant of quant * binder list * term
  | Tattr of string * term
  | Tlet of pat * term * term
  | Tmatch of term * (pat * term) list
  | Tcast of term * pty
  | Ttuple of term list
  | Told of term

type header = { hd_name : id; hd_ret : labelled_arg list; hd_args : labelled_arg list }
(** The header of a contract: [r = f x y], with ghost arguments in brackets. *)

type contract = {
  header : header option;
  atomic : bool;  (** A logically atomic contract: [atomic f x]. *)
  requires : term list;
  ensures : term list;
  atomic_requires : term list;
  atomic_ensures : term list;
  variant : term list;
  pure : bool;
}

let empty_contract =
  {
    header = None;
    atomic = false;
    requires = [];
    ensures = [];
    atomic_requires = [];
    atomic_ensures = [];
    variant = [];
    pure = false;
  }

type loop_spec = { invariants : term list; loop_variant : term list }
(** The specification of a loop, written at the start of its body. *)

type predicate = {
  pred_name : id;
  pred_params : (id * pty) list;
  pred_body : term option;  (** [None] for a declaration in an interface. *)
}
(** A predicate, [predicate p (x : t) ... = body]. *)

(** A ghost statement in code. *)
type ghost_stmt = Fold of term | Unfold of term | Assert of term

let mk_loc (s, e) = { Location.loc_start = s; loc_end = e; loc_ghost = false }
let mk_term t l = { term_desc = t; term_loc = l }

(** The application of the operator [op] to [args]. *)
let mk_op_apply op args =
  let f = mk_term (Tvar (Qid op)) op.pid_loc in
  let t = List.fold_left (fun f arg -> mk_term (Tapply (f, arg)) arg.term_loc) f args in
  t.term_desc

(** [t] with a chain of infix operations, as [e1 < e2 <= e3], desugared into a
    conjunction, as [e1 < e2 && e2 <= e3]. *)
let rec chain t =
  match t.term_desc with
  | Tinfix (t1, o, t2) ->
      begin match t2.term_desc with
      | Tinfix (t3, _, _) ->
          let t = chain t2 in
          let conj = mk_id ~fixity:Infix ~loc:Location.none "&&" in
          let infix = mk_term (mk_op_apply o [ t1; t3 ]) t.term_loc in
          mk_term (mk_op_apply conj [ infix; t ]) t.term_loc
      | _ -> mk_term (mk_op_apply o [ t1; t2 ]) t.term_loc
      end
  | _ -> t

let chain_desc t = (chain { term_desc = t; term_loc = Location.none }).term_desc
