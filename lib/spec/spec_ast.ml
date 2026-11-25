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

exception Syntax_error of Location.t * string

let mk_id ?(fixity = Normal) ?(attrs = []) ~loc str =
  { pid_str = str; pid_fixity = fixity; pid_attrs = attrs; pid_loc = loc }

let add_attr id attr = { id with pid_attrs = attr :: id.pid_attrs }

type qualid = Qid of id | Qdot of qualid * id
type ghost_module = { ghost_module_name : id; ghost_module_interface : qualid }

let rec qualid_loc = function Qid id -> id.pid_loc | Qdot (_, id) -> id.pid_loc

type row_bound = Closed_row | Lower_row | Upper_row

type pty =
  | PTtyany
  | PTtyvar of id
  | PTtyapp of qualid * pty list
  | PTtuple of pty list
  | PTarrow of pty * pty
  | PTvariant of row_bound * id list

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
  | Tquant of quant * binder list * triggers * term
      (** [forall x y [t1, t2 | t3]. body], with alternative triggers of one or more
          terms. *)
  | Tcomprehension of (id * pty) * term
  | Tattr of string * term
  | Tlet of pat * term * term
  | Tmatch of term * (pat * term) list
  | Tcast of term * pty
  | Ttuple of term list
  | Trecord of term option * (id * term) list
      (** A record, [{ f = e; ... }], or one updating another, [{ r with f = e; ... }]. *)
  | Told of term

and triggers = term list list

let rec is_mask_wildcard term =
  match term.term_desc with
  | Tvar (Qid id) -> id.pid_str = "_"
  | Tcast (term, _) -> is_mask_wildcard term
  | _ -> false

type header = { hd_name : id; hd_ret : labelled_arg list; hd_args : labelled_arg list }
(** The header of a contract: [r = f x y], with ghost arguments in brackets. *)

type contract = {
  header : header option;
  atomic : bool;  (** A logically atomic contract: [atomic f x]. *)
  requires : term list;
  ensures : term list;
  atomic_requires : term list;
  atomic_ensures : term list;
  raises : (pat * term option) list;
      (** The exceptions the function may raise, as patterns, each with what holds when it
          raises it: [raises E x -> t]. *)
  atomic_raises : (pat * term) list;
      (** What holds atomically when the function linearizes by raising an exception:
          [atomic raises E -> t]. *)
  variant : term list;
  opens : (Location.t * term list) option;
      (** [None] infers the footprint; an explicit empty clause keeps it closed. *)
  pure : bool;
  continues : id option;
      (** The function whose atomic update a local function continues, [continues push]:
          it takes that function's parameters first, and has its contract too. *)
}

let empty_contract =
  {
    header = None;
    atomic = false;
    requires = [];
    ensures = [];
    atomic_requires = [];
    atomic_ensures = [];
    raises = [];
    atomic_raises = [];
    variant = [];
    opens = None;
    pure = false;
    continues = None;
  }

type loop_spec = {
  invariants : term list;
  state_invariants : (pat list * term) list;
  loop_variant : term list;
  loop_raises : (pat * term option) list;
      (** What holds when the loop stops by raising an exception: [raises E x -> t]. *)
  invariant_witnesses : (id * term) list;
      (** The values that names the invariants bind take after each iteration:
          [with { x = e }]. *)
}
(** The specification of a loop, written at the start of its body. *)

type ancestry_kind = Parent | Within

type invariant_ancestry = {
  ancestry_kind : ancestry_kind;
  ancestry_target : qualid;
  ancestry_args : id list;
  ancestry_loc : Location.t;
}

type predicate = {
  pred_name : id;
  pred_params : (id * pty) list;
  pred_body : term option;  (** [None] for a declaration in an interface. *)
  pred_persistent : bool;
      (** An invariant declaration, duplicable and distinct from ordinary predicates. *)
  pred_inline : bool;  (** [[@inline]]: its uses are its body, never folded. *)
  pred_ancestry : invariant_ancestry option;
}
(** A predicate, [predicate p (x : t) ... = body]. *)

let ancestry_application ancestry =
  let term term_desc = { term_desc; term_loc = ancestry.ancestry_loc } in
  List.fold_left
    (fun head argument -> term (Tapply (head, term (Tvar (Qid argument)))))
    (term (Tvar ancestry.ancestry_target))
    ancestry.ancestry_args

type state_field = {
  sf_name : id;
  sf_type : pty;
  sf_grows : bool;
  sf_helps : string option;
}
(** A field of the ghost state; [[@grows]] if it only grows: sequences by prefix, integers
    by [<=]. *)

(** A ghost statement in code. *)
type ghost_stmt =
  | Fold of term
  | Unfold of term
  | Assert of term
  | Cut of term
      (** Proves its assertion, and verifies the rest from that assertion alone. *)
  | Fold_with of term * (id * term) list
  | Unfold_with of term * (id * term) list
  | Ghost_call of term

type proof_expr = { proof_desc : proof_desc; proof_loc : Location.t }

and proof_desc =
  | Proof_value of term
  | Proof_let of pat * proof_expr * proof_expr
  | Proof_seq of proof_expr * proof_expr
  | Proof_if of term * proof_expr * proof_expr
  | Proof_match of term * (pat * proof_expr) list
  | Proof_assert of term
  | Proof_cut of term
  | Proof_fold of term * (id * term) list
  | Proof_unfold of term * id list

type initialization =
  | Initial_record of (id * term) list
  | Initial_let of pat * proof_expr * initialization

type scope_mode =
  | General_scope
  | Frozen_scope
  | Published_scope
  | Release_scope
  | Acquire_scope

type access_scope = {
  scope_mode : scope_mode;
  scope_operation : id;
  scope_state : pat option;
  scope_body : proof_expr;
}

type return_adapter = {
  returns_result : pat;
  returns_state : pat;
  returns_body : proof_expr;
}

type proof_module_argument =
  | Proof_type_argument of { type_params : id list; type_body : pty }
  | Proof_module_argument of qualid

type proof_module_parameter =
  | Proof_named_parameter of id * qualid
  | Proof_unit_parameter of Location.t

type access_kind = Frozen | Relaxed

(** The definition of a proof's type. *)
type type_kind =
  | Variant of (id * pty list) list
  | Record of (id * pty) list
      (** A logical record, [type piece = { before : int list; next : node }]. *)
  | Alias of pty

(** The names that [p] binds. *)
let rec pat_names (p : pat) =
  match p.pat_desc with
  | Pwild | Pconst _ | Pconstr (_, None) -> []
  | Pid id -> [ id.pid_str ]
  | Ptuple ps -> List.concat_map pat_names ps
  | Pcast (p, _) | Pconstr (_, Some p) -> pat_names p

(** A step of a proof outline: ghost code at a place in a function, written in the
    [.proof] file as [at (anchor) step] or [on return e]. *)
type outline_step =
  | At of {
      anchor_loc : Location.t;
      action : step_action;
      action_loc : Location.t;
      export : pat option;
          (** [let p = at ...]: the value the scope returns with the result, for the later
              steps. *)
    }
  | Let of { pattern : pat; value : proof_expr }
      (** [let p = e in ...]: pure ghost code for the later steps, which run it where they
          use it. *)
  | On_return of { return_loc : Location.t; return_adapter : bool }
      (** Ghost code when the function returns. *)
  | Initially of { initialization_loc : Location.t }
      (** The constructor's initial shared state. *)
  | Nested of outline  (** The outline of a local function. *)

(** What a step does at its code. *)
and step_action =
  | Linearize  (** [commit], [returning p -> commit] or [performs a]. *)
  | Scope  (** A proof around the access or call, [(fun step -> e)]. *)
  | Wrapped_scope  (** An explicit Ghost wrapper around an access or call. *)
  | Initializes  (** The ghost fields of an allocation, [initializes [...]]. *)
  | Loop  (** An invariant at the first expression of a loop body. *)

and outline = {
  outline_name : id;
  outline_params : id list option;  (** The parameters that select the function. *)
  outline_contract : Location.t option;
  outline_steps : outline_step list;
  outline_loc : Location.t;
}
(** The proof of a function, [proof f x = steps], in program order. A function without a
    contract in the interface gives it in the header, [proof r = f x requires p = steps].
*)

(** A declaration of a proof. *)
type helped_result = {
  contents : pat option;
      (** The pattern that the key's contents after the action match, binding what the
          result uses, [as Next (v, _)]. *)
  result : term;
}
(** The result with which an action commits the calls it helps. *)

type proof_decl =
  | Proof_module of {
      module_name : id;
      module_parameters : proof_module_parameter list;
      module_declarations : proof_decl list;
      module_outlines : outline list;
      module_loc : Location.t;
    }
  | Proof_definition of {
      module_name : id;
      module_interface : qualid;
      module_constraints : (id list * id * pty) list;
      module_declarations : proof_decl list;
      module_outlines : outline list;
      module_loc : Location.t;
    }
  | Proof_predicate of predicate
  | Proof_type of {
      type_name : id;
      type_params : id list;
      type_kind : type_kind;
      type_recursive : bool;
    }
  | Proof_resource of {
      resource_name : id;
      resource_functor : qualid;
      resource_arguments : proof_module_argument list;
    }
  | Proof_au of { au_name : id; au_operation : qualid }
  | Proof_task of { task_name : id; task_operation : qualid }
  | Proof_access_field of {
      access_name : id;
      access_kind : access_kind;
      access_owner : pat * pty;
      access_selector : term;
    }
  | Proof_field of { field_name : id; field_type : pty }
  | Proof_function of {
      function_name : id;
      function_params : (id * pty) list;
      function_result : pty;
      function_recursive : bool;
      function_variant : term list;
      function_body : term;
    }
  | Proof_lemma of {
      lemma_name : id;
      lemma_params : (id * pty) list;
      lemma_returns : (id * pty) list;
      lemma_requires : term list;
      lemma_ensures : (triggers * term) list;
          (** Postconditions with their triggers, which only an auto lemma's have:
              [ensures [t]. p]. *)
      lemma_variant : term list;
      lemma_opens : (Location.t * term list) option;
      lemma_body : proof_expr;
    }
  | Proof_state of {
      state_name : id;
      state_params : id list;
      state_fields : state_field list;
    }
      (** The ghost state of a structure, [type state = { items : int list }], which an
          invariant's last parameter has. Other record types are logical records. *)
  | Proof_invariant of {
      inv_name : id;
      inv_params : (id * pty) list;
      inv_state : id * pty;
      inv_body : term;
      inv_ancestry : invariant_ancestry option;
    }
      (** The persistent predicate [inv_name], defined by the heap in terms of the state,
          [invariant is_stack (t : t) (s : state) = own t s.items]. *)
  | Proof_view of { view_name : id; view_params : (id * pty) list; view_value : term }
      (** The exclusive predicate [view_name]: a client's view of the state,
          [view stack (t : t) = s.items], whose last parameter is the value. *)
  | Proof_action of {
      action_name : id;
      action_params : id list;
      action_step : (id * term option list) option;
      action_consumes : term option;
      action_state : id;
      action_update : (id * term) list;
      action_linearizes : id list;
      action_helps : (term * term * helped_result) list;
          (** The calls it helps: those waiting in pending fields on keys, with the
              results, [helps s.waiting on last s.cells with false]. *)
    }
      (** A transition of the state, as
          [action pop = compare_and_set q.head s.cells.(s.head) s.cells.(s.head + 1) ~> {
           s with head = s.head + 1 } linearizes pop_opt]: its parameters, the step that
          performs it, an operation with its arguments, [_] for any, what the step gives
          the state, the fields it changes, in terms of the state before, and the
          functions it linearizes. Without a step, only [(*@ performs a *)] names it. *)

type proof_file = { declarations : proof_decl list; outlines : outline list }

(** What an atomic step does to the update of the function that performs it, if its result
    matches a pattern: linearize it, with the function's result or a given one, leave it
    to be helped, as [wait in s.waiting on c], or either, by a condition. *)
type outcome =
  | Commits
  | Commits_with of term
  | Waits of term * term  (** The pending field and the key it waits on. *)
  | Chooses of term * outcome * outcome

(** Where an atomic step linearizes the function that performs it: always, or if its
    result matches a pattern, as [returning [] -> commit]. *)
type linearization = Commit | Returning of pat * outcome | Performs of id

let mk_loc (s, e) = { Location.loc_start = s; loc_end = e; loc_ghost = false }
let mk_term t l = { term_desc = t; term_loc = l }

(** The terms of a record: what it updates, if anything, then its field values. *)
let record_terms base fields = Option.to_list base @ List.map snd fields

(** The terms of postconditions with triggers, the triggers' included. *)
let postcondition_terms ensures =
  List.concat_map (fun (triggers, t) -> t :: List.concat triggers) ensures

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

(** The element, state binder and field of [past (mem element state.field)]. *)
let past_membership term =
  let rec split arguments term =
    match (chain term).term_desc with
    | Tapply (callee, argument) -> split (argument :: arguments) callee
    | _ -> (term, arguments)
  in
  match split [] term with
  | { term_desc = Tvar (Qid { pid_str = "past"; _ }); _ }, [ fact ] ->
      begin match split [] fact with
      | ( { term_desc = Tvar (Qid { pid_str = "mem"; _ }); _ },
          [
            element;
            { term_desc = Tfield ({ term_desc = Tvar (Qid state); _ }, Qid field); _ };
          ] ) ->
          Some (element, state, field)
      | _ -> None
      end
  | _ -> None
