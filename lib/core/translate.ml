(** The translation of OCaml implementations to Raven programs.

    So far: top-level functions on integers, booleans, unit, tuples and variant types,
    with their contracts. A function becomes a procedure, and a variant type a data type
    (see {!Datatypes}). Expressions are put in A-normal form, since a call is a statement
    in Raven; arguments are evaluated right to left, as OCaml does. *)

open Base
module R = Raven_api

type error = Report.error

module S = Caravan_spec.Spec_ast

(** The head of the application [t] and its arguments. *)
let rec spine (t : S.term) args =
  match t.term_desc with Tapply (f, a) -> spine f (a :: args) | _ -> (t, args)

(** The conjuncts of [t]. *)
let rec conjuncts (t : S.term) =
  let t = S.chain t in
  match spine t [] with
  | { term_desc = Tvar (Qid { pid_str = "&&" | "/\\"; _ }); _ }, [ a; b ] ->
      conjuncts a @ conjuncts b
  | _ -> [ t ]

(** The conjuncts of [terms] that make a variable a field of a value, [x == g.f] or
    [g.f == x]: the variable, the field and the value's name. *)
let field_equations (terms : S.term list) =
  List.filter_map (List.concat_map terms ~f:conjuncts) ~f:(fun t ->
      match spine t [] with
      | { term_desc = Tvar (Qid { pid_str = "=" | "==" | "==="; _ }); _ }, [ a; b ] ->
          begin match (a.term_desc, b.term_desc) with
          | ( Tvar (Qid { pid_str = x; _ }),
              Tfield
                ({ term_desc = Tvar (Qid { pid_str = g; _ }); _ }, Qid { pid_str = f; _ })
            )
          | ( Tfield
                ({ term_desc = Tvar (Qid { pid_str = g; _ }); _ }, Qid { pid_str = f; _ }),
              Tvar (Qid { pid_str = x; _ }) ) ->
              Some (x, f, g)
          | _ -> None
          end
      | _ -> None)

(** The elements of the list literal [t], if it is one. *)
let rec list_literal (t : S.term) =
  match spine t [] with
  | { term_desc = Tvar (Qid { pid_str = "[]"; _ }); _ }, [] -> Some []
  | { term_desc = Tvar (Qid { pid_str = "::"; _ }); _ }, [ h; rest ] ->
      Option.map (list_literal rest) ~f:(fun rest -> h :: rest)
  | _ -> None

let ( let* ) = Result.( >>= )
let error ?related loc message = Error (Report.error ?related Type loc message)
let unsupported = Report.unsupported
let loc (l : Location.t) = R.Loc.make l.loc_start l.loc_end
let ident ~loc name = R.Ident.make ~loc name
let name ~loc n = R.Name.make ~loc n
let qualified_name ~loc text = Qualified_name.raven ~loc (Qualified_name.of_string text)

(** [f] mapped over [xs], stopping at the first error. *)
let all (xs : 'a list) ~(f : 'a -> ('b, error) Result.t) : ('b list, error) Result.t =
  Result.all (List.map xs ~f)

let is_unit (t : Types.type_expr) =
  match Types.get_desc t with
  | Tconstr (p, [], _) -> Path.same p Predef.path_unit
  | _ -> false

let is_int (t : Types.type_expr) =
  match Types.get_desc t with
  | Tconstr (p, [], _) -> Path.same p Predef.path_int
  | _ -> false

(** That the value of [x] is in the range of OCaml's [int], if its type is [int]. *)
let range_spec ~loc:l (t : Types.type_expr) x =
  Option.some_if (is_int t)
    (R.Spec.make
       (R.Expr.call ~loc:l
          (R.Name.make ~loc:l Prelude.in_range)
          [ R.Expr.var ~loc:l (R.Name.make ~loc:l x) ]))

(** That [x] is in the range of OCaml's [int], if its type [t] is [int]: true of every
    value, since every [int] the translation creates is checked to be. *)
let assume_in_range ~loc:l (t : Types.type_expr) x =
  Option.value_map (range_spec ~loc:l t x) ~default:[] ~f:(fun spec ->
      [ R.Stmt.assume ~loc:l spec ])

(** The names of a function's variables in Raven: OCaml's, made distinct where a name is
    bound twice. *)
module Names = struct
  type t = {
    mutable used : Set.M(String).t;
    mutable bound : (string * string) list;
    mutable scope : (string * (string * Types.type_expr option)) list;
        (** The variables bound so far, by their OCaml names, latest first, with their
            Raven names and types. *)
  }

  let create () = { used = Set.empty (module String); bound = []; scope = [] }

  (** A name for [base] not used yet. *)
  let fresh names base =
    let rec go n =
      let candidate = if n = 0 then base else Printf.sprintf "%s_%d" base n in
      if Set.mem names.used candidate then go (n + 1) else candidate
    in
    let name = go 0 in
    names.used <- Set.add names.used name;
    name

  (** The Raven name of the OCaml variable [id] of type [typ], bound now. *)
  let bind ?typ names (id : Ident.t) =
    let name = fresh names (Ident.name id) in
    names.bound <- (Ident.unique_name id, name) :: names.bound;
    names.scope <- (Ident.name id, (name, typ)) :: names.scope;
    name

  let find names (id : Ident.t) =
    List.Assoc.find names.bound (Ident.unique_name id) ~equal:String.equal
end

type origin = {
  at : Location.t;
  code : R.Diagnostic.code;
  message : string;
  related : (Location.t * string) list;
}
(** A check the translation generates, with the code of its failure, and what it checks,
    as the message and related locations to report when it fails. *)

type action = {
  action : string;
  params : string list;
  step : (string * S.term option list) option;
      (** The operation performing it, with its arguments: the location, then the others,
          [None] for any. *)
  state : string;
  update : (string * S.term) list;  (** The fields it changes. *)
  linearizes : Ident.t list;
  helps : (string * S.term * S.term) option;
      (** The pending field whose calls it helps, the key and the result. *)
  action_at : Location.t;
}
(** An action of a structure (see {!S.Proof_action}). *)

type performing = { performed : action; bindings : (string * R.Expr.t) list }
(** An action that a step performs, with the values of its parameters. *)

type pending = {
  pending_field : string;
  pending_on : string;  (** The existential of the keys of the registrations. *)
  key_type : Types.type_expr;
  helped : Ident.t;  (** The function whose calls wait. *)
  helping : string * S.term * S.term;
      (** The key whose calls the action that helps commits, and the result, in terms of
          the state before the action, named as the action names it. *)
}
(** A field of calls of [helped] waiting to be helped, each registered on a key: a finite
    set of registrations, ghost cells holding the calls' updates. *)

(** Whether a function with an atomic contract has linearized, as far as the translation
    knows. Raven needs the atomic update in the same state after both arms of a branch, so
    a step whose effect depends on its result leaves the update open, and the arms of the
    branch on that result close it. *)
type au_state =
  | Pending  (** Not linearized, the update closed. *)
  | Committed
  | Committing
      (** Linearized, the update open until the function's result is known, at the end of
          the arm whose value it is. *)
  | On_cas  (** The update open, linearized if the last [compare_and_set] succeeded. *)
  | On_read of string
      (** The update open, linearized if the value of the last read has this constructor.
      *)
  | Partly  (** Linearized on some paths, the update closed. *)
  | Registered of registered
      (** Linearized, or left to be helped if [registered] says so: given away in a
          registration on a pending field, whose result a later step collects. *)
  | Unknown

and registered = {
  registration : R.Expr.t;  (** The ghost cell of the registration. *)
  registered : R.Expr.t;  (** Whether the call registered rather than linearized. *)
  pending_inv : string;
  pending : pending;
}

(** How the atomic update closes. *)
type au_close =
  | Commit  (** The step linearized the function. *)
  | Abort  (** The step did not change the abstract state. *)
  | Commit_call  (** The step is a call, which linearized the function in its place. *)

type au = {
  mutable state : au_state;
  mutable cas_results : (string * bool) list;
      (** Variables bound to the result of a [compare_and_set], or its negation if
          [false], by their unique names. *)
  mutable read_results : string list;
      (** Variables bound to the value of the last read, by their unique names. *)
  mutable values : R.Expr.t list;
      (** The values of the implicit parameters in the open update. *)
  mutable step : Location.t;  (** The step that opened the update. *)
  mutable performing : (performing * R.Expr.t option) option;
      (** The action that the step performs if it commits, as [(*@ performs pop *)] or by
          its step, with the condition, if any, under which the step is the action's. *)
  self : string;  (** The procedure's name. *)
  role : Ident.t;
      (** The function that the update is of: [self], or the one it continues. *)
  ghost_results : R.Expr.t list;
      (** The ghost results witnessing facts about earlier states, which the update
          commits with. *)
  has_result : bool;
  open_ :
    at:Location.t -> unfold:bool -> (R.Stmt.t list * R.Expr.t list, Report.error) Result.t;
      (** Opens the atomic update for the step at [at]: the statements, unfolding the
          atomic precondition's predicates if [unfold], and the values of the implicit
          parameters. *)
  close : au_close -> value:R.Expr.t -> (R.Stmt.t list, Report.error) Result.t;
      (** Closes the open update, committing with the function's result [value]. *)
  token : R.Expr.t;  (** The update's token. *)
  commit_only : at:Location.t -> value:R.Expr.t -> (R.Stmt.t list, Report.error) Result.t;
      (** Opens the update and commits it with [value] at once, at the step at [at], the
          invariants left as they are. *)
}
(** The atomic update of a function with an atomic contract. *)

type lemma_signature = {
  lemma_raven : string;
  lemma_constant : bool;
  lemma_inputs : Types.type_expr list;
  lemma_implicit_count : int;
  lemma_outputs : Types.type_expr list;
}

type procedure_signature = {
  procedure_inputs : (string * Types.type_expr) list;
  procedure_outputs : (string * Types.type_expr) list;
  procedure_result : Types.type_expr;
}

type atomic_shape = {
  inputs : Types.type_expr list;
  result : Types.type_expr;
  ghost_outputs : Types.type_expr list;
  implicit : Types.type_expr list;
}

type atomic_signature = {
  au_key : string;
  au_owner : Path.t option;
  au_private : atomic_shape;
  au_token : Types.type_expr;
  au_source : Source.proof_au;
  au_procedure : string;
  au_inputs : Types.type_expr list;
  au_result : Types.type_expr;
  au_ghost_outputs : Types.type_expr list;
  au_implicit : Types.type_expr list;
}

type proof_support = {
  runtime_functions : Qualified_name.t Path_bindings.t;
  predicate_views : string Path_bindings.t;
  public_types : Path.t list;
  strict_source_types : bool;
  library_paths : string list Path_bindings.t;
  atomic_updates : atomic_signature list;
  resources : Source.proof_resource list;
  ghost_fields : Source.proof_field list;
  canonical_path : Path.t -> Path.t;
  logical_functions : (string * lemma_signature) list;
  mathematical_types : Datatypes.t list;
  predicate_inputs : (string * int) list;
      (** Explicit overrides of the type-based predicate output convention. *)
  proof_key : Env.t -> S.qualid -> string option;
  action_key : S.id -> string option;
  opaque_predicates : string list;
}

let empty_proof_support =
  {
    runtime_functions = Path_bindings.empty;
    predicate_views = Path_bindings.empty;
    public_types = [];
    strict_source_types = false;
    library_paths = Path_bindings.empty;
    atomic_updates = [];
    resources = [];
    ghost_fields = [];
    canonical_path = Fn.id;
    logical_functions = [];
    mathematical_types = [];
    predicate_inputs = [];
    proof_key = (fun _ _ -> None);
    action_key = (fun _ -> None);
    opaque_predicates = [];
  }

type declaration_context = {
  declaration_predicates : (string * (string * Types.type_expr list)) list;
  declaration_functions : (string * string) list;
  declaration_support : proof_support;
}

type structure = {
  context : declaration_context;
  scope : Proof_scopes.scope option;
  environment : Env.t;
  invariant : string;
  backend : string;
  state : string;
  fields : (string * string * R.Type.t * Types.type_expr * bool) list;
  chains : (string * string) list;
  actions : action list;
  pendings : pending list;
  held : (S.term * string * S.term) list;
      (** The atomics that the invariant owns holding an entry of a field owned by index,
          [own q.head s.cells.(s.head)]: the atomic, the field and the position. *)
  params : (string * Types.type_expr) list;
      (** The invariant's parameters but the state, with their types. *)
  structure_type : Types.type_expr;
  views : (S.predicate * S.term) list;  (** The views, with their values. *)
  at : Location.t;  (** The invariant's definition. *)
}
(** A structure whose invariant has a ghost state: the invariant, its state variable, the
    state's fields with their existentials, Raven and OCaml types and whether they grow,
    the fields indexing ownership, with the existentials of their index maps, the actions,
    and the type of the structure, the invariant's first parameter. *)

let has_history st = List.exists st.fields ~f:(fun (_, _, _, _, grows) -> grows)

(** The type of the index map of [field] of [st], owned by index: from its entries to
    their positions. *)
let chain_index_type types st field =
  let l = R.Loc.none in
  let elt =
    match List.find st.fields ~f:(fun (f, _, _, _, _) -> String.equal f field) with
    | Some (_, _, _, t, _) ->
        begin match Datatypes.desc types t with
        | Tconstr (_, [ elt ], _) -> Result.ok (Datatypes.typ types ~at:Location.none elt)
        | _ -> None
        end
    | None -> None
  in
  R.Type.map ~loc:l (Option.value elt ~default:(R.Type.ref ~loc:l)) (R.Type.int ~loc:l)

(** The values of the fields of [st] that grow, among [values], those of all its fields:
    the history's state. *)
let grown st values =
  List.filter_map (List.zip_exn st.fields values) ~f:(fun ((_, _, _, _, grows), v) ->
      Option.some_if grows v)

(** The names of the members generated for [st]: functions, lemmas and fields, and
    modules. *)
let member_name st suffix =
  let backend = Qualified_name.of_string st.backend in
  Qualified_name.to_string { backend with name = backend.name ^ "_" ^ suffix }

let module_name st suffix =
  let backend = Qualified_name.of_string st.backend in
  Qualified_name.to_string
    { backend with name = String.capitalize backend.name ^ "_" ^ suffix }

let generated_ident ~loc text = ident ~loc (Qualified_name.of_string text).name

let generated_module_member ~loc module_name member =
  let module_name = Qualified_name.of_string module_name in
  R.Name.make ~loc ~path:(module_name.path @ [ module_name.name ]) member

(** The names of the members generated for the pending field [p] of [st]. *)
let pending_name st (p : pending) suffix = member_name st (p.pending_field ^ "_" ^ suffix)

type past = { inv : string; field : string; element : S.term }
(** A fact about an earlier state of a structure, [past (mem e s.f)]: [e] was in the field
    [f], owned by index, of a state of the invariant [inv], which a snapshot of its
    history and a position in [f] witness. *)

(** [t] as a fact about an earlier state, if it is one, of the structures [structures]. *)
let past_of structures (t : S.term) =
  Option.bind (S.past_membership t) ~f:(fun (element, state, field) ->
      match
        List.filter structures ~f:(fun st ->
            String.equal st.state state.pid_str
            && List.Assoc.mem st.chains field.pid_str ~equal:String.equal)
      with
      | [ st ] -> Some { inv = st.invariant; field = field.pid_str; element }
      | [] | _ :: _ :: _ -> None)

(** The state of the growing fields [values] of [st], as the history holds it. *)
let state_of ~loc:l st values =
  R.Expr.call ~loc:l
    (generated_module_member ~loc:l (module_name st "state") "state")
    values

(** That the snapshot [snapshot] of [st]'s history, on the structure [structure], has the
    value [e] at the position [k] of its field [field]. *)
let past_fact ~loc:l st ~structure ~field ~snapshot ~k e =
  let qn m x = generated_module_member ~loc:l m x in
  let entries = R.Expr.field ~loc:l snapshot (qualified_name ~loc:l field) in
  let bin op a b = R.Expr.binary ~loc:l op a b in
  List.reduce_exn ~f:(bin And)
    [
      R.Expr.own ~loc:l
        [
          structure;
          R.Expr.call ~loc:l
            (qn (module_name st "history") "frag")
            [
              R.Expr.call ~loc:l
                (qn (module_name st "states") "set")
                [ R.Expr.set ~loc:l [ snapshot ] ];
            ];
        ];
      bin Leq (R.Expr.int ~loc:l 0) k;
      bin Lt k (R.Expr.call ~loc:l (qn "Seq" "length") [ entries ]);
      bin Eq (R.Expr.index ~loc:l entries k) e;
    ]

type shared = {
  persistent : (string * Location.t) list;
      (** The invariants, by their names, with their definitions. *)
  views : (string * string) list;
      (** The views, by their names, with their ghost fields, which hold a client's view
          of the state, half in the view and half in the invariant. *)
  structures : structure list;
  member_aliases : (string * string) list;
  mutable dynamic_indices : bool;
  anchors : (string * (string * R.Type.t * R.Expr.t option) list) list;
      (** The ghost fields of the views and histories, by the field whose allocation
          allocates them, the field of the structure's reference, with their initial
          values: arbitrary for views. *)
}
(** The shared structures of a program: invariants and views. *)

(** The ghost field holding the client's view [v] of a state. *)

let view_field key = "view_" ^ key

let view_field_in shared key =
  Option.value
    (List.Assoc.find shared.views key ~equal:String.equal)
    ~default:(view_field key)

let canonical_member shared member =
  Option.value
    (List.find_map shared.member_aliases ~f:(fun (alias, target) ->
         Option.map
           (String.chop_prefix member ~prefix:(alias ^ "."))
           ~f:(fun suffix -> target ^ "." ^ suffix)))
    ~default:member

let no_shared =
  {
    persistent = [];
    views = [];
    structures = [];
    member_aliases = [];
    anchors = [];
    dynamic_indices = false;
  }

type opened = { values : R.Expr.t list; indices : (string * R.Expr.t) list }
(** The state of an open invariant: the variables of its fields and of the index maps of
    the fields owned by index. *)

type position = {
  pos_inv : string;
  pos_field : string;
  pos_element : R.Expr.t;
  pos_snapshot : R.Expr.t;
  pos_k : R.Expr.t;
}
(** That [pos_element] is at the position [pos_k] of the field [pos_field], owned by
    index, of the snapshot [pos_snapshot] of the history of the invariant [pos_inv]. *)

let implicit_parameter_count ~kind parameters =
  let rec check seen count = function
    | [] -> Ok (if seen then Some count else None)
    | (id, _) :: rest ->
        let implicit = List.mem id.S.pid_attrs "implicit" ~equal:String.equal in
        if seen && not implicit then
          error id.pid_loc
            (Printf.sprintf "Implicit %s parameters must follow explicit parameters" kind)
        else check (seen || implicit) (if implicit then count + 1 else count) rest
  in
  check false 0 parameters

let predicate_output_count ?has_refs data (predicate : S.predicate) types =
  let* explicit = implicit_parameter_count ~kind:"predicate" predicate.pred_params in
  match explicit with
  | Some _ when predicate.pred_persistent ->
      error predicate.pred_name.pid_loc
        "Implicit parameter annotations require an ordinary predicate"
  | Some count -> Ok count
  | None when predicate.pred_persistent -> Ok 0
  | None ->
      let has_refs = Option.value has_refs ~default:(Datatypes.has_refs data) in
      let count =
        List.length (List.take_while (List.rev types) ~f:(fun typ -> not (has_refs typ)))
      in
      Ok (if count = List.length types then 0 else count)

type predicate_body = {
  definition : S.term;
  environment : Env.t;
  project_type : Types.type_expr -> Types.type_expr;
}

type context = {
  types : Datatypes.t list;
  refs : (string * R.Member.t) list ref;
      (** The fields of the ref cells and atomics used so far, by their names, with their
          declarations. *)
  primitives : (string * R.Member.t) list ref;
      (** The atomic operations used so far, by their names (see {!Primitives}). *)
  primitive_namespace : string list;
  names : Names.t;
  functions : string Path_bindings.t;
      (** Checked functions, indexed by their compiler paths. *)
  pasts : (string * (string * string * int) list) list;
      (** The facts about earlier states that procedures require, by their names: the
          invariant, the field, and the position of the parameter that was in it. *)
  past_returns :
    (string * (string * string * (R.Expr.t list -> R.Expr.t option)) list) list;
      (** The facts about earlier states that procedures ensure, by their names, each
          witnessed by two ghost results: the invariant, the field, and the entry, given
          the arguments, if it is known. *)
  lifted : (string * (int * Ident.t list * Ident.t option)) list;
      (** The lifted local functions, by their procedures' names, with the number of
          parameters of the function they continue, which they take first, the variables
          of their context they use, which they take next, and the function's identity. *)
  ghost_args : (string * (int * string) option list) list;
      (** The ghost parameters of procedures, by their names: for each, the position of a
          parameter that a precondition makes a field of it, with the field, as [tail] in
          [requires tail = q.tail], by which calls find the ghost argument. *)
  procedure_signatures : (string * procedure_signature) list;
  mutable ghost_returns : (string * string * Types.type_expr) list;
  mutable proof_state : (R.Expr.t * Types.type_expr) option;
  mutable return_covered : bool;
  mutable fields_of : (string * (string * R.Expr.t)) list;
      (** The variables known to be fields of values, by their Raven names: the field and
          the value, as [tail] of [q] after [let push { tail; _ } value]. *)
  libraries : string list Path_bindings.t;
      (** The modules of the libraries, with their names: trusted Raven modules. *)
  mutable formals : R.Expr.t list;
      (** The procedure's parameters, of which a lifted local function that continues it,
          or that it continues too, takes the first. *)
  origins : origin list ref;
  annotations : Annotation.t list;  (** Those of the file, as loops' invariants. *)
  proof_lemmas : (string * lemma_signature) list;
  proof_support : proof_support;
  predicate_bodies : (string * predicate_body) list;
      (** Explicit predicate bodies, for the types of named unfold witnesses. *)
  spec_funcs : (string * string) list;
      (** The functions contracts can call, by their OCaml names, with their Raven ones.
      *)
  env : Env.t;  (** OCaml's, for the types in annotations. *)
  preds : (string * (string * Types.type_expr list)) list;
      (** The predicates, by their OCaml names, with their Raven names and parameter
          types. *)
  mutable facts : R.Spec.t list;
      (** Facts that hold throughout the function: its preconditions without [own], which
          only mention variables, all immutable. *)
  mutable au : au option;
      (** The atomic update, for a function with an atomic contract. *)
  current_procedure : string option;
  manual : bool;
  access_proofs : ((int * int) * Annotation.t) list;
  return_proofs : ((int * int) * Annotation.t) list;
  initializations : ((int * int) * Annotation.t) list;
  linearizations : (int * Annotation.t) list;
      (** The annotations on atomic steps, by the offset of the end of the step they
          follow. *)
  shared : shared;
  mutable invariants : (string * R.Expr.t list) list;
      (** The invariants that the function's precondition holds, opened around each of its
          atomic steps, with their arguments. *)
  mutable opened : (string * opened) list;  (** The states of the open invariants. *)
  mutable snapshots : (string * opened list) list;
      (** The snapshots of the states of the invariants taken on the current path, latest
          first. *)
  mutable positions : position list;
      (** The positions of entries in snapshots known on the current path. *)
}

let typ ctx ~at t = Datatypes.typ ctx.types ~at t

(** Declares [field], with values of type [elt], unless it is already. *)
let declare_field ctx ~at field elt =
  let* t = typ ctx ~at elt in
  if not (List.Assoc.mem !(ctx.refs) field ~equal:String.equal) then begin
    let file = { Lexing.dummy_pos with pos_fname = at.Location.loc_start.pos_fname } in
    let loc = R.Loc.make file file in
    ctx.refs :=
      !(ctx.refs) @ [ (field, Datatypes.field_member ctx.types ~loc field t elt) ]
  end;
  Ok ()

(** The field of the ref cells with contents of type [elt]. *)
let ref_field ctx ~at elt =
  let field = "ref_" ^ Datatypes.tag ctx.types elt ^ "_contents" in
  let* () = declare_field ctx ~at field elt in
  Ok field

(** The field of the atomics with contents of type [elt]. *)
let atomic_field ctx ~at elt =
  let field = "atomic_" ^ Datatypes.tag ctx.types elt in
  let* () = declare_field ctx ~at field elt in
  Ok field

(** The procedure performing [op] on the atomics with contents of type [elt]. *)
let primitive ctx ~at elt op =
  let* field = atomic_field ctx ~at elt in
  let name = Primitives.name ~field op in
  let* typ = typ ctx ~at elt in
  if not (List.Assoc.mem !(ctx.primitives) name ~equal:String.equal) then
    ctx.primitives :=
      !(ctx.primitives)
      @ [
          ( name,
            Primitives.proc ~field ~typ
              ~exact:(Datatypes.immediate ctx.types elt)
              ~int:(Datatypes.is_int ctx.types elt)
              op );
        ];
  Ok name

(** The ordinary read or write of a mutable field. *)
let ordinary_primitive ctx ~at ~field elt op =
  let stem = String.uncapitalize (String.concat ~sep:"_" (String.split field ~on:'.')) in
  let declaration_name = Primitives.ordinary_name ~field:stem op in
  let procedure =
    String.concat ~sep:"." (ctx.primitive_namespace @ [ declaration_name ])
  in
  let* typ = typ ctx ~at elt in
  if not (List.Assoc.mem !(ctx.primitives) procedure ~equal:String.equal) then
    ctx.primitives :=
      !(ctx.primitives)
      @ [
          ( procedure,
            Primitives.ordinary_proc ~declaration_name ~field ~typ
              ~int:(Datatypes.is_int ctx.types elt)
              op );
        ];
  Ok procedure

(** The Raven field named [label] of the values of type [t] that are references; an
    atomic's contents have the empty label, as in [own a v]. *)
let field_of_type ctx ~at (t : Types.type_expr) label =
  match Datatypes.desc ctx.types t with
  | Tconstr (p, [ elt ], _) when Datatypes.is_ref p && String.equal label "contents" ->
      let* field = ref_field ctx ~at elt in
      Ok (Some field)
  | Tconstr (p, [ elt ], _) when Datatypes.is_atomic p && String.is_empty label ->
      let* field = atomic_field ctx ~at elt in
      Ok (Some field)
  | Tconstr (p, [], _) ->
      begin match Datatypes.find ctx.types p with
      | Some { heap = Some fields; _ } ->
          Ok
            (Option.map
               (List.find fields ~f:(fun f -> String.equal f.label label))
               ~f:(fun f -> f.raven_field))
      | _ -> Ok None
      end
  | _ -> Ok None

(** The atomic that the field [label] of a value of the immutable record type [t] holds:
    its type, if it is one. *)
let atomic_in_record ctx (t : Types.type_expr) label =
  match Datatypes.desc ctx.types t with
  | Tconstr (p, [], _) ->
      begin match Datatypes.find ctx.types p with
      | Some { heap = None; ctors = [ { ocaml = ""; fields; args; _ } ]; _ } ->
          List.find_map (List.zip_exn fields args) ~f:(fun (f, a) ->
              match Datatypes.desc ctx.types a with
              | Tconstr (q, [ _ ], _) when String.equal f label && Datatypes.is_atomic q
                ->
                  Some a
              | _ -> None)
      | _ -> None
      end
  | _ -> None

(** The OCaml type of the field [label] of values of type [t] that are references, or of
    the contents of an atomic an immutable record holds. *)
let backend_field_type ctx (t : Types.type_expr) label =
  match atomic_in_record ctx t label with
  | Some atomic ->
      begin match Datatypes.desc ctx.types atomic with
      | Tconstr (_, [ elt ], _) -> Some elt
      | _ -> None
      end
  | None -> (
      match Datatypes.desc ctx.types t with
      | Tconstr (p, [ elt ], _) when Datatypes.is_ref p && String.equal label "contents"
        ->
          Some elt
      | Tconstr (p, [ elt ], _) when Datatypes.is_atomic p && String.is_empty label ->
          Some elt
      | Tconstr (p, [], _) ->
          begin match Datatypes.find ctx.types p with
          | Some { heap = Some fields; _ } ->
              Option.map
                (List.find fields ~f:(fun f -> String.equal f.label label))
                ~f:(fun f -> f.typ)
          | _ -> None
          end
      | _ -> None)

(** Uses the source declaration before expanding implementation aliases. *)
let source_field_type ctx t label =
  try
    match Types.get_desc (Ctype.expand_head ctx.env t) with
    | Tconstr (path, [ element ], _)
      when Datatypes.is_atomic path && String.is_empty label ->
        Some element
    | Tconstr (path, args, _) -> (
        let declaration = Env.find_type path ctx.env in
        match declaration.type_kind with
        | Type_record (fields, _) ->
            Option.map
              (List.find fields ~f:(fun field ->
                   String.equal (Ident.name field.Types.ld_id) label))
              ~f:(fun field ->
                Ctype.apply ctx.env declaration.type_params field.ld_type args)
        | _ -> None)
    | _ -> None
  with Stdlib.Not_found -> None

let field_type ctx t label =
  Option.map (backend_field_type ctx t label) ~f:(fun fallback ->
      match source_field_type ctx t label with
      | None -> fallback
      | Some source ->
          if Option.is_some (atomic_in_record ctx t label) then
            match Types.get_desc (Ctype.expand_head ctx.env source) with
            | Tconstr (path, [ element ], _) when Datatypes.is_atomic path -> element
            | _ -> fallback
          else source)

(** The Raven field of the record field [label], and whether its record is a reference;
    [None] if it is unknown. *)
let field_of_label ctx ~at (label : Data_types.label_description) =
  match Types.get_desc label.lbl_res with
  | Tconstr (p, [ elt ], _) when Datatypes.is_ref p ->
      let* field = ref_field ctx ~at elt in
      Ok (Some (field, true))
  | _ ->
      begin match Datatypes.find_label ctx.types label with
      | Some { heap = Some fields; _ } ->
          let field =
            List.find_exn fields ~f:(fun f -> String.equal f.label label.lbl_name)
          in
          Ok (Some (field.raven_field, true))
      | Some _ -> Ok (Some (label.lbl_name, false))
      | None -> Ok None
      end

(** The assertion [c] checking, at [at], what [message] says may fail. *)
let check ctx ~(at : Location.t) message c =
  ctx.origins := { at; code = Assertion; message; related = [] } :: !(ctx.origins);
  R.Stmt.assert_ ~loc:(loc at) (R.Spec.make c)

(** The check that the value [v] of an [int] operation, at [at], does not overflow. *)
let no_overflow ctx ~at what v =
  let l = loc at in
  let bound op n = R.Expr.binary ~loc:l op v (R.Expr.int ~loc:l n) in
  check ctx ~at
    (Printf.sprintf "This %s may overflow" what)
    (R.Expr.binary ~loc:l And (bound Geq Prelude.min_int) (bound Leq Prelude.max_int))

let prelude_call ~loc:l f args = R.Expr.call ~loc:l (name ~loc:l f) args

(** The write of [v] to the field [field] of the reference [r]. *)
let write ~loc:l r field v =
  R.Stmt.assign ~loc:l
    [ R.Expr.field ~loc:l r (qualified_name ~loc:l field) ]
    (R.Stmt.expr_rhs v)

let ordinary_read ?guard ctx ~at ~field ~elt r =
  let l = loc at in
  let* proc = ordinary_primitive ctx ~at ~field elt Primitives.Read in
  let* typ = typ ctx ~at elt in
  let x = Names.fresh ctx.names "tmp" in
  let value = R.Expr.var ~loc:l (name ~loc:l x) in
  let rhs = R.Stmt.expr_rhs (R.Expr.call ~loc:l (qualified_name ~loc:l proc) [ r ]) in
  let access =
    match guard with
    | None -> R.Stmt.local ~loc:l ~typ ~init:rhs (ident ~loc:l x)
    | Some condition ->
        R.Stmt.local ~loc:l ~typ (ident ~loc:l x)
        @ [ R.Stmt.if_ ~loc:l condition [ R.Stmt.assign ~loc:l [ value ] rhs ] [] ]
  in
  Ok (access, value)

let ordinary_write ctx ~at ~field ~elt r v =
  let l = loc at in
  let* proc = ordinary_primitive ctx ~at ~field elt Primitives.Write in
  Ok (R.Stmt.call ~loc:l (R.Expr.call ~loc:l (qualified_name ~loc:l proc) [ r; v ]))

(** The name of [p] if it is a value of the standard library's toplevel. *)
let stdlib_name (p : Path.t) =
  match p with
  | Pdot (Pident m, x) when Ident.persistent m && String.equal (Ident.name m) "Stdlib" ->
      Some x
  | _ -> None

(** The name of [p] if it is a value of [Stdlib.Atomic]. *)
let atomic_name (p : Path.t) =
  match p with
  | Pdot (Pdot (Pident m, "Atomic"), x)
    when Ident.persistent m && String.equal (Ident.name m) "Stdlib" ->
      Some x
  | Pdot (Pident m, x)
    when Ident.persistent m && String.equal (Ident.name m) "Stdlib__Atomic" ->
      Some x
  | _ -> None

(** The operators of the standard library that Raven has, by their paths. *)
let binop_of_path (p : Path.t) : R.Expr.binop option =
  match stdlib_name p with
  | Some "+" -> Some Plus
  | Some "-" -> Some Minus
  | Some "*" -> Some Mult
  | Some "/" -> Some Div
  | Some "mod" -> Some Mod
  | Some ("=" | "==") -> Some Eq
  | Some ("<>" | "!=") -> Some Neq
  | Some "<" -> Some Lt
  | Some "<=" -> Some Leq
  | Some ">" -> Some Gt
  | Some ">=" -> Some Geq
  | Some "&&" -> Some And
  | Some "||" -> Some Or
  | _ -> None

(** Whether [==] or [!=] on [a] and [b] is equality or its negation: on immediate values,
    and with a constant constructor, which is immediate. Otherwise, physical equality
    implies equality, but not conversely. *)
let exact_physical types (a : Typedtree.expression) (b : Typedtree.expression) =
  let constant (e : Typedtree.expression) =
    match e.exp_desc with Texp_construct (_, _, []) -> true | _ -> false
  in
  Datatypes.immediate types a.exp_type || constant a || constant b

let runtime_nullary_constructor (e : Typedtree.expression) =
  match e.exp_desc with Texp_construct (_, _, []) -> true | _ -> false

let rec unresolved_equality_type types ty =
  match Datatypes.desc types ty with
  | Tvar _ | Tunivar _ -> true
  | Tconstr (_, args, _) -> List.exists args ~f:(unresolved_equality_type types)
  | Ttuple components ->
      List.exists components ~f:(fun (_, ty) -> unresolved_equality_type types ty)
  | Tpoly (ty, []) -> unresolved_equality_type types ty
  | _ -> false

let potentially_contains_refs types ty =
  Datatypes.has_refs types ty || unresolved_equality_type types ty

let runtime_structural_equality_unsafe ctx path a b =
  match stdlib_name path with
  | Some ("=" | "<>") ->
      (not (runtime_nullary_constructor a || runtime_nullary_constructor b))
      && (potentially_contains_refs ctx.types a.exp_type
         || potentially_contains_refs ctx.types b.exp_type)
  | _ -> false

let mathematical_type ctx (t : Types.type_expr) =
  match Datatypes.desc ctx.types t with
  | Tconstr (p, _, _) ->
      Option.is_some (Datatypes.collection_kind ctx.types p)
      || List.exists ctx.proof_support.mathematical_types ~f:(fun d ->
          Datatypes.declares d p)
  | _ -> false

let spec_contains_runtime_refs ctx ty =
  let rec go seen ty =
    if mathematical_type ctx ty then false
    else
      match Datatypes.desc ctx.types ty with
      | Tvar _ | Tunivar _ -> true
      | Tconstr (p, [ _ ], _) when Datatypes.is_ref p || Datatypes.is_atomic p -> true
      | Tconstr (p, [], _) when Datatypes.is_ghost p -> true
      | Tconstr (p, args, _) ->
          List.exists args ~f:(go seen)
          || begin match Datatypes.find ctx.types p with
          | Some { heap = Some _; _ } -> true
          | Some { library = Some _; _ } -> true
          | Some ({ id = Some id; _ } as d) when not (List.mem seen id ~equal:Ident.same)
            ->
              List.exists d.ctors ~f:(fun c -> List.exists c.args ~f:(go (id :: seen)))
          | _ -> false
          end
      | Ttuple components -> List.exists components ~f:(fun (_, ty) -> go seen ty)
      | Tpoly (ty, []) -> go seen ty
      | _ -> false
  in
  go [] ty

let is_physical (p : Path.t) =
  match stdlib_name p with Some ("==" | "!=") -> true | _ -> false

let unop_of_path (p : Path.t) =
  match stdlib_name p with Some "not" -> Some `Not | Some "~-" -> Some `Neg | _ -> None

let unit_value ~loc = R.Expr.tuple ~loc []

(** The arguments of an application, if all are given and unlabelled. *)
let plain_args ~at (args : (Asttypes.arg_label * Typedtree.apply_arg) list) =
  all args ~f:(function
    | Nolabel, Arg e -> Ok e
    | _ -> unsupported at "A labelled, optional or omitted argument")

(** What a name in a contract stands for: a Raven variable, or a value, such as the field
    of a matched value that a pattern names. *)
type bound =
  | Raven of string
  | Value of R.Expr.t
  | State of (string * (R.Expr.t * Types.type_expr)) list
      (** The state of an invariant, by the values and types of its fields. *)

type env = {
  ctx : context;  (** For the data types, and the fields of ref cells. *)
  var_types : (string * Types.type_expr) list;
      (** The OCaml types of variables, if known. *)
  data : Datatypes.t list;
  funcs : (string * string) list;
      (** The functions contracts can call, by their OCaml names, with their Raven ones.
      *)
  vars : (string * bound) list;
  logical_definition : bool;
}

let bind env x b = { env with vars = (x, b) :: env.vars }

(** The operators of contracts that Raven has. *)
let spec_binop (op : string) : R.Expr.binop option =
  match op with
  | "+" -> Some Plus
  | "-" -> Some Minus
  | "*" -> Some Mult
  | "/" -> Some Div
  | "mod" -> Some Mod
  | "=" | "==" | "===" -> Some Eq
  | "<>" | "!=" | "=/=" -> Some Neq
  | "<" -> Some Lt
  | "<=" -> Some Leq
  | ">" -> Some Gt
  | ">=" -> Some Geq
  | "&&" | "/\\" -> Some And
  | "||" | "\\/" -> Some Or
  | "->" -> Some Impl
  | "<->" -> Some Iff
  | _ -> None

(** The complete source spelling of a specification identifier. *)
let qualid_key q = Qualified_name.to_string (Qualified_name.of_spec q)

let resolved_call functions libraries path =
  match Path_bindings.find functions path with
  | Some name -> Some name
  | None -> Option.map (Path_bindings.member libraries path) ~f:Qualified_name.to_string

let library_paths libraries =
  Path_bindings.of_list
    (List.map libraries ~f:(fun (lib : Library_modules.t) ->
         (lib.library_path, [ lib.library_name ])))

let runtime_spec env q =
  Option.bind (Source.value_path env.ctx.env q) ~f:(fun path ->
      Path_bindings.find env.ctx.proof_support.runtime_functions path)

let atomic_method env = function
  | S.Qdot (parent, method_) ->
      Option.bind (Source.module_path env.ctx.env parent) ~f:(fun path ->
          let path = env.ctx.proof_support.canonical_path path in
          Option.map
            (List.find env.ctx.proof_support.atomic_updates ~f:(fun signature ->
                 Source.au_has_path signature.au_source path))
            ~f:(fun signature -> (signature, method_.pid_str)))
  | Qid _ -> None

let logical_key env q =
  let atomic_key =
    Option.bind (atomic_method env q) ~f:(fun (signature, method_) ->
        Option.some_if
          (List.mem [ "pending"; "committed" ] method_ ~equal:String.equal)
          (signature.au_key ^ "." ^ method_))
  in
  match Option.first_some atomic_key (env.ctx.proof_support.proof_key env.ctx.env q) with
  | Some key -> key
  | None ->
      begin match q with
      | S.Qid _ -> qualid_key q
      | Qdot (parent, id) ->
          let view =
            Option.bind (Source.module_path env.ctx.env parent) ~f:(fun path ->
                Path_bindings.find env.ctx.proof_support.predicate_views
                  (Path.Pdot (path, id.pid_str)))
          in
          begin match view with
          | Some key -> key
          | None ->
              begin match
                Option.bind
                  (Source.module_path env.ctx.env parent)
                  ~f:(Path_bindings.find env.ctx.proof_support.library_paths)
              with
              | None -> qualid_key q
              | Some path ->
                  Qualified_name.to_string Qualified_name.{ path; name = id.pid_str }
              end
          end
      end

let find_constructor env q =
  Option.bind (Source.constructor env.ctx.env q) ~f:(Datatypes.find_cstr env.data)

(** The functions of OCaml's standard library on lists that contracts can use, as Raven's
    [List]'s. *)
let list_function : S.qualid -> string option = function
  | Qdot (Qid { pid_str = "List"; _ }, { pid_str = "length"; _ }) -> Some "len"
  | Qdot (Qid { pid_str = "List"; _ }, { pid_str = "mem"; _ }) -> Some "in"
  | _ -> None

(** Logical collections have no runtime module or OCaml representation. *)
let collection_builtin env (q : S.qualid) =
  match q with
  | Qdot (Qid m, f)
    when List.mem [ "Finset"; "Set"; "Map" ] m.pid_str ~equal:String.equal
         && not (List.Assoc.mem env.funcs (qualid_key q) ~equal:String.equal) ->
      Some (m.pid_str, f.pid_str)
  | _ -> None

let atomic_inputs signature method_ =
  let token = signature.au_token in
  match method_ with
  | "bind" -> Some ([ Predef.type_unit ], [ token ])
  | "access" -> Some (token :: signature.au_inputs, signature.au_implicit)
  | "abort" -> Some (token :: signature.au_inputs, [])
  | "commit" ->
      Some
        ( (token :: signature.au_inputs)
          @ (signature.au_result :: signature.au_ghost_outputs),
          [] )
  | "pending" -> Some (token :: signature.au_inputs, [ Predef.type_bool ])
  | "committed" ->
      Some
        ( (token :: signature.au_inputs)
          @ (signature.au_result :: signature.au_ghost_outputs),
          [ Predef.type_bool ] )
  | _ -> None

(** Raven takes the concrete inputs and outputs as tuples, including empty ones. *)
let atomic_arguments ~loc:l signature method_ values =
  match values with
  | [] -> []
  | token :: rest ->
      let inputs, outputs = List.split_n rest (List.length signature.au_inputs) in
      let inputs = R.Expr.tuple ~loc:l inputs in
      if List.mem [ "commit"; "committed" ] method_ ~equal:String.equal then
        let outputs =
          if is_unit signature.au_result then List.drop outputs 1 else outputs
        in
        [ token; inputs; R.Expr.tuple ~loc:l outputs ]
      else [ token; inputs ]

let resource_module env parent =
  Option.bind (Source.module_path env.ctx.env parent) ~f:(fun path ->
      let path = env.ctx.proof_support.canonical_path path in
      List.find env.ctx.proof_support.resources ~f:(fun resource ->
          Source.resource_has_path resource path))

let resource_operation env = function
  | S.Qdot (parent, operation) ->
      Option.bind (resource_module env parent) ~f:(fun resource ->
          List.find_map resource.resource_operations ~f:(fun (name, inputs, result) ->
              Option.some_if
                (String.equal name operation.pid_str)
                {
                  lemma_raven = resource.resource_backend ^ "." ^ name;
                  lemma_constant =
                    List.mem resource.resource_constants name ~equal:String.equal;
                  lemma_inputs = inputs;
                  lemma_implicit_count = 0;
                  lemma_outputs = [ result ];
                }))
  | Qid _ -> None

let logical_signature env q =
  match q with
  | S.Qid id when List.Assoc.mem env.vars id.pid_str ~equal:String.equal -> None
  | _ ->
      begin match resource_operation env q with
      | Some _ as signature -> signature
      | None ->
          List.Assoc.find env.ctx.proof_support.logical_functions (logical_key env q)
            ~equal:String.equal
      end

let ghost_descriptor env q =
  Option.bind (Source.value_path env.ctx.env q) ~f:(fun path ->
      let path = env.ctx.proof_support.canonical_path path in
      List.find env.ctx.proof_support.ghost_fields ~f:(fun field ->
          Path.same path field.Source.field_path || Path.same path (Pident field.field_id)))

let shadowed_ghost_descriptor env = function
  | S.Qid id -> List.Assoc.mem env.vars id.pid_str ~equal:String.equal
  | Qdot _ -> false

let ghost_projection env t =
  match spine t [] with
  | { S.term_desc = Tvar (Qdot (Qid m, op)); _ }, [ { term_desc = Tvar field; _ }; owner ]
    when String.equal m.pid_str "Ghost"
         && String.equal op.pid_str "at"
         && not (shadowed_ghost_descriptor env field) ->
      Option.map (ghost_descriptor env field) ~f:(fun descriptor -> (descriptor, owner))
  | _ -> None

let ghost_field_name (field : Source.proof_field) =
  let name = Qualified_name.of_string field.field_backend in
  Qualified_name.to_string { name with name = "proof$" ^ name.name }

let ghost_operation t =
  match spine t [] with
  | { S.term_desc = Tvar (Qdot (Qid m, op)); _ }, _ when String.equal m.pid_str "Ghost" ->
      Some op.pid_str
  | _ -> None

let is_ghost_fpu t = Option.equal String.equal (ghost_operation t) (Some "fpu")

let same_named_type left right =
  match (Types.get_desc left, Types.get_desc right) with
  | Tconstr (left, [], _), Tconstr (right, [], _) -> Path.same left right
  | _ -> false

let resource_field env (field : Source.proof_field) =
  Option.exists field.field_resource ~f:(fun owner ->
      List.exists env.ctx.proof_support.resources ~f:(fun resource ->
          resource.resource_is_ra && Source.resource_has_path resource owner))
  || List.exists env.ctx.proof_support.resources ~f:(fun resource ->
      resource.resource_is_ra && same_named_type field.field_value resource.resource_type)

(** The variable, field and name of [own x.label v], with the empty label for [own x v].
*)
let owned_location (t : S.term) =
  match spine t [] with
  | ( { term_desc = Tvar (Qid { pid_str = "own"; _ }); _ },
      [ location; { term_desc = Tvar (Qid { pid_str = v; _ }); _ } ] ) ->
      begin match location.term_desc with
      | Tfield ({ term_desc = Tvar (Qid { pid_str = x; _ }); _ }, Qid label) ->
          Some (x, label.pid_str, v)
      | Tvar (Qid { pid_str = x; _ }) -> Some (x, "", v)
      | _ -> None
      end
  | _ -> None

let is_constructor x =
  String.equal x "[]" || String.equal x "::"
  || ((not (String.is_empty x)) && Char.is_uppercase x.[0])

let nullary_constructor (t : S.term) =
  let head, args = spine t [] in
  match (head.term_desc, args) with
  | Tvar (Qid { pid_str = constructor; _ }), [] -> is_constructor constructor
  | _ -> false

(** The arguments of a constructor of [arity], given as [args]: a tuple for several. *)
let ctor_args ~at arity (args : 'a list) ~(tuple : 'a -> 'a list option) =
  match (arity, args) with
  | n, args when List.length args = n -> Ok args
  | n, [ a ] when n > 1 ->
      begin match tuple a with
      | Some components when List.length components = n -> Ok components
      | _ -> error at (Printf.sprintf "This constructor expects %d arguments" n)
      end
  | n, _ -> error at (Printf.sprintf "This constructor expects %d arguments" n)

(** The variables bound by a specification pattern. *)
let rec pat_names (p : S.pat) =
  match p.pat_desc with
  | Pwild | Pconst _ | Pconstr (_, None) -> []
  | Pid id -> [ id.pid_str ]
  | Ptuple ps -> List.concat_map ps ~f:pat_names
  | Pcast (p, _) | Pconstr (_, Some p) -> pat_names p

(** The names that the contract term [t] uses free. *)
let rec term_names (t : S.term) : string list =
  let without bound names =
    List.filter names ~f:(fun x -> not (List.mem bound x ~equal:String.equal))
  in
  match t.term_desc with
  | Ttrue | Tfalse | Tconst _ | Tvar (Qdot _) -> []
  | Tvar (Qid id) -> [ id.pid_str ]
  | Tapply (a, b) | Tinfix (a, _, b) -> term_names a @ term_names b
  | Tif (a, b, c) -> term_names a @ term_names b @ term_names c
  | Tquant (_, binders, body) ->
      without (List.map binders ~f:(fun (id, _) -> id.S.pid_str)) (term_names body)
  | Tcomprehension ((id, _), body) -> without [ id.pid_str ] (term_names body)
  | Tlet (p, a, b) -> term_names a @ without (pat_names p) (term_names b)
  | Tmatch (t, cases) ->
      term_names t
      @ List.concat_map cases ~f:(fun (p, body) ->
          without (pat_names p) (term_names body))
  | Ttuple ts -> List.concat_map ts ~f:term_names
  | Tattr (_, t) | Tcast (t, _) | Told t | Tfield (t, _) -> term_names t

let rec term_references bound (t : S.term) =
  let refs = term_references bound in
  match t.term_desc with
  | Tvar (Qid id) when List.mem bound id.pid_str ~equal:String.equal -> []
  | Tvar q -> [ q ]
  | Ttrue | Tfalse | Tconst _ -> []
  | Tapply (a, b) | Tinfix (a, _, b) -> refs a @ refs b
  | Tif (a, b, c) -> refs a @ refs b @ refs c
  | Tquant (_, binders, body) ->
      term_references (List.map binders ~f:(fun (id, _) -> id.S.pid_str) @ bound) body
  | Tcomprehension ((id, _), body) -> term_references (id.pid_str :: bound) body
  | Tlet (p, a, b) -> refs a @ term_references (pat_names p @ bound) b
  | Tmatch (t, cases) ->
      refs t
      @ List.concat_map cases ~f:(fun (p, b) -> term_references (pat_names p @ bound) b)
  | Ttuple ts -> List.concat_map ts ~f:refs
  | Tattr (_, t) | Tcast (t, _) | Told t | Tfield (t, _) -> refs t

(** The location of the first occurrence of the name [x] in [terms]. *)
let name_loc (terms : S.term list) x ~default =
  let rec find (t : S.term) =
    match t.term_desc with
    | Tvar (Qid id) when String.equal id.pid_str x -> Some id.pid_loc
    | Tapply (a, b) | Tinfix (a, _, b) -> Option.first_some (find a) (find b)
    | Tif (a, b, c) -> List.find_map [ a; b; c ] ~f:find
    | Tquant (_, _, t)
    | Tcomprehension (_, t)
    | Tattr (_, t)
    | Tcast (t, _)
    | Told t
    | Tfield (t, _) ->
        find t
    | Tlet (_, a, b) -> Option.first_some (find a) (find b)
    | Tmatch (t, cases) ->
        Option.first_some (find t) (List.find_map cases ~f:(fun (_, b) -> find b))
    | Ttuple ts -> List.find_map ts ~f:find
    | _ -> None
  in
  Option.value (List.find_map terms ~f:find) ~default

(** The names free in [terms] that [env] does not bind, with Raven names for them, and
    their OCaml and Raven types: a name owned as the value of a field has that field's
    type, as [n] in [own c.count n]. *)
let free_typed ?(lenient = false) env (terms : S.term list) ~at =
  let is_name x =
    (not (String.is_empty x))
    && (Char.is_lowercase x.[0] || Char.equal x.[0] '_')
    && String.for_all x ~f:(fun c ->
        Char.is_alphanum c || Char.equal c '_' || Char.equal c '\'')
  in
  let logical_names =
    List.concat_map terms ~f:(term_references [])
    |> List.filter_map ~f:(function
      | S.Qid id as q ->
          let key = logical_key env q in
          Option.some_if
            (List.Assoc.mem env.ctx.preds key ~equal:String.equal
            || List.Assoc.mem env.ctx.proof_support.logical_functions key
                 ~equal:String.equal
            || List.Assoc.mem env.ctx.proof_lemmas key ~equal:String.equal)
            id.pid_str
      | Qdot _ -> None)
  in
  let known x =
    List.Assoc.mem env.vars x ~equal:String.equal
    || List.Assoc.mem env.funcs x ~equal:String.equal
    || List.mem logical_names x ~equal:String.equal
    || Option.is_some (ghost_descriptor env (S.Qid (S.mk_id ~loc:at x)))
    || List.mem
         [
           "own";
           "not";
           "max_int";
           "min_int";
           "mod";
           "length";
           "last";
           "drop";
           "take";
           "to_sequence";
         ]
         x ~equal:String.equal
  in
  let free =
    List.concat_map terms ~f:term_names
    |> List.filter ~f:(fun x -> is_name x && not (known x))
    |> List.dedup_and_sort ~compare:String.compare
  in
  (* The types of the values of fields that [t] owns; and of names passed to predicates. *)
  let rec owned (t : S.term) =
    match (owned_location t, S.(t.term_desc)) with
    | Some (x, label, v), _ ->
        Option.to_list
          (Option.bind (List.Assoc.find env.var_types x ~equal:String.equal)
             ~f:(fun typ ->
               Option.map (field_type env.ctx typ label) ~f:(fun t -> (v, t))))
    | None, (Tapply (a, b) | Tinfix (a, _, b)) -> owned a @ owned b
    | None, Tif (a, b, c) -> owned a @ owned b @ owned c
    | None, (Tattr (_, t) | Tcast (t, _)) -> owned t
    | None, _ -> []
  in
  let passed =
    Spec_arguments.predicate_parameters ~bound:[] terms ~lookup:(fun q ->
        Option.map
          (List.Assoc.find env.ctx.preds (logical_key env q) ~equal:String.equal)
          ~f:snd)
    |> List.map ~f:(fun (id, typ) -> (id.S.pid_str, typ))
  in
  let owned = List.concat_map terms ~f:owned @ passed in
  let* typed =
    all free ~f:(fun x ->
        match List.Assoc.find owned x ~equal:String.equal with
        | None when lenient -> Ok None
        | None ->
            error (name_loc terms x ~default:at) (Printf.sprintf "Unbound name %s" x)
        | Some t ->
            let l = loc at in
            let* typ = typ env.ctx ~at t in
            let raven = Names.fresh env.ctx.names x in
            Ok (Some (x, raven, t, typ, l)))
  in
  Ok (List.filter_opt typed)

(** The fields of the state [x], if [x] is one. *)
let state_fields env x =
  match List.Assoc.find env.vars x ~equal:String.equal with
  | Some (State fields) -> Some fields
  | _ -> None

(** Whether a local module has a hidden representation in this lexical environment. *)
let opaque_module_path env path =
  match path with
  | Path.Pdot _ ->
      Option.exists (Datatypes.find env.ctx.types path) ~f:(fun data ->
          (Option.is_some data.id
          || List.mem env.ctx.proof_support.public_types path ~equal:Path.same)
          &&
            try
              let declaration = Env.find_type path env.ctx.env in
              (match declaration.type_kind with
                | Types.Type_abstract _ -> true
                | _ -> false)
              && Option.is_none declaration.type_manifest
              || Poly.equal declaration.type_private Asttypes.Private
            with Stdlib.Not_found -> false)
  | Pident _ | Papply _ | Pextra_ty _ -> false

let opaque_module_types env =
  env.ctx.proof_support.strict_source_types
  || List.exists env.ctx.types ~f:(fun data ->
      List.exists data.Datatypes.paths ~f:(opaque_module_path env))

(** The formula [t] of a contract. *)
let rec formula (env : env) (t : S.term) : (R.Expr.t, error) Result.t =
  let* () =
    if opaque_module_types env then
      Signature_contract.expression ~logical_types:env.data ~environment:env.ctx.env
        ~predicates:(fun q ->
          Option.map
            (List.Assoc.find env.ctx.preds (logical_key env q) ~equal:String.equal)
            ~f:snd)
        ~variables:env.var_types t
    else Ok ()
  in
  let at = t.term_loc in
  let l = loc at in
  match t.term_desc with
  | Ttrue -> Ok (R.Expr.bool ~loc:l true)
  | Tfalse -> Ok (R.Expr.bool ~loc:l false)
  | Tconst (Pconst_integer (n, None)) -> Ok (R.Expr.int ~loc:l (Int.of_string n))
  | Tconst _ -> unsupported at "This constant"
  | Tvar (Qid { pid_str = x; _ }) when is_constructor x -> constructor env t []
  | Tvar (Qdot (_, id)) when is_constructor id.pid_str -> constructor env t []
  | Tvar q when Option.is_some (logical_signature env q) ->
      logical_application env ~at (Option.value_exn (logical_signature env q)) []
  | Tvar (Qid { pid_str = x; _ })
    when List.Assoc.mem env.ctx.proof_support.predicate_inputs x ~equal:String.equal
         && not (List.Assoc.mem env.vars x ~equal:String.equal) ->
      application env t
  | Tvar (Qid { pid_str = x; _ }) ->
      begin match (List.Assoc.find env.vars x ~equal:String.equal, x) with
      | Some (Raven x), _ -> Ok (R.Expr.var ~loc:l (name ~loc:l x))
      | Some (Value v), _ -> Ok v
      | Some (State _), _ ->
          error at (Printf.sprintf "The state %s is used by its fields, as %s.f" x x)
      | None, "max_int" -> Ok (R.Expr.int ~loc:l Prelude.max_int)
      | None, "min_int" -> Ok (R.Expr.int ~loc:l Prelude.min_int)
      | None, _ -> error at (Printf.sprintf "Unbound name %s" x)
      end
  | Tvar q when Option.is_some (collection_builtin env q) ->
      collection_application env ~at (Option.value_exn (collection_builtin env q)) []
  | Tvar q when Option.is_some (resource_operation env q) ->
      logical_application env ~at (Option.value_exn (resource_operation env q)) []
  | Tvar (Qdot (parent, _) as q) when Option.is_some (resource_module env parent) ->
      error at ("Unknown proof module member " ^ qualid_key q)
  | Tvar (Qdot (Qid m, v))
    when String.equal m.pid_str "Permission"
         && List.mem [ "half"; "full" ] v.pid_str ~equal:String.equal ->
      Ok (R.Expr.real ~loc:l (if String.equal v.pid_str "half" then 0.5 else 1.0))
  | Tvar (Qdot _) -> unsupported at "A qualified name"
  | Tinfix _ -> formula env (S.chain t)
  | Tapply _ -> application env t
  | Tif (c, a, b) ->
      let* c = formula env c in
      let* a = formula env a in
      let* b = formula env b in
      Ok (R.Expr.ite ~loc:l c a b)
  | Tquant (q, binders, body) ->
      let* bound =
        all binders ~f:(fun (id, ty) ->
            match ty with
            | None -> error id.pid_loc "A bound variable needs a type, as in x: int"
            | Some ty ->
                let* t = Source.ocaml_type env.ctx.env ~at:id.pid_loc ty in
                let* ty = typ env.ctx ~at:id.pid_loc t in
                let l = loc id.pid_loc in
                let raven =
                  if env.logical_definition then Names.fresh env.ctx.names id.pid_str
                  else id.pid_str
                in
                Ok (id.pid_str, raven, t, R.Var.make ~loc:l (ident ~loc:l raven) ty))
      in
      let env =
        List.fold bound ~init:env ~f:(fun env (x, raven, t, _) ->
            { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
      in
      let* body = formula env body in
      let vars = List.map bound ~f:(fun (_, _, _, v) -> v) in
      (* A variable of type [int] ranges over its values. *)
      let ranges =
        List.filter_map bound ~f:(fun (_, x, t, _) ->
            Option.map (range_spec ~loc:l t x) ~f:(fun _ ->
                R.Expr.call ~loc:l
                  (R.Name.make ~loc:l Prelude.in_range)
                  [ R.Expr.var ~loc:l (R.Name.make ~loc:l x) ]))
      in
      let guard = List.reduce ranges ~f:(fun a b -> R.Expr.binary ~loc:l And a b) in
      Ok
        (match (q, guard) with
        | Tforall, None -> R.Expr.forall ~loc:l vars body
        | Tforall, Some g -> R.Expr.forall ~loc:l vars (R.Expr.binary ~loc:l Impl g body)
        | Texists, None -> R.Expr.exists ~loc:l vars body
        | Texists, Some g -> R.Expr.exists ~loc:l vars (R.Expr.binary ~loc:l And g body))
  | Tcomprehension ((id, ty), body) ->
      let* ty = Source.ocaml_type env.ctx.env ~at:id.pid_loc ty in
      let* raven_type = typ env.ctx ~at:id.pid_loc ty in
      let raven = Names.fresh env.ctx.names id.pid_str in
      let env =
        {
          (bind env id.pid_str (Raven raven)) with
          var_types = (id.pid_str, ty) :: env.var_types;
          logical_definition = true;
        }
      in
      let* body = formula env body in
      let body =
        match range_spec ~loc:l ty raven with
        | None -> body
        | Some _ ->
            R.Expr.binary ~loc:l And
              (R.Expr.call ~loc:l
                 (name ~loc:l Prelude.in_range)
                 [ R.Expr.var ~loc:l (name ~loc:l raven) ])
              body
      in
      Ok
        (R.Expr.set_compr ~loc:l (R.Var.make ~loc:l (ident ~loc:l raven) raven_type) body)
  | Ttuple ts ->
      let* ts = all ts ~f:(formula env) in
      Ok (R.Expr.tuple ~loc:l ts)
  | Tmatch (scrutinee, cases) ->
      let* v = formula env scrutinee in
      let* scrutinee_type =
        Result.map (equality_term_type env scrutinee) ~f:Option.some
      in
      spec_match env ~at ?scrutinee_type v cases
  | Tattr (_, t) -> formula env t
  | Tcast (t, ty) ->
      let* ty = Source.ocaml_type env.ctx.env ~at ty in
      let* raven_type = typ env.ctx ~at ty in
      let* value = expected_formula env (Some ty) t in
      Ok (R.Expr.annotated value raven_type)
  | Tfield ({ term_desc = Tvar (Qid { pid_str = x; _ }); _ }, Qid { pid_str = label; _ })
    when Option.is_some (state_fields env x) ->
      begin match
        List.Assoc.find (Option.value_exn (state_fields env x)) label ~equal:String.equal
      with
      | Some (v, _) -> Ok v
      | None -> error at (Printf.sprintf "The state %s has no field %s" x label)
      end
  | Tfield (r, Qid { pid_str = label; _ }) ->
      let reference =
        match r.term_desc with
        | Tvar (Qid { pid_str = x; _ }) ->
            (* An atomic that an immutable record holds is a value, read by Atomic.get. *)
            Option.bind (List.Assoc.find env.var_types x ~equal:String.equal) ~f:(fun t ->
                if Option.is_some (atomic_in_record env.ctx t label) then None
                else Option.map (field_type env.ctx t label) ~f:(fun _ -> x))
        | _ -> None
      in
      begin match reference with
      | Some x ->
          error at
            (Printf.sprintf "A contract reads %s.%s through own, as in own %s.%s v" x
               label x label)
      | None ->
          let* r = formula env r in
          Ok (R.Expr.field ~loc:l r (qualified_name ~loc:l label))
      end
  | Tfield (_, Qdot _) -> unsupported at "A qualified field"
  | Tlet (pattern, value, body) ->
      let* translated = formula env value in
      let* condition, bindings = spec_pattern env pattern translated in
      let* () =
        match condition with
        | None -> Ok ()
        | Some _ -> error pattern.pat_loc "A logical let needs an irrefutable pattern"
      in
      let types =
        Option.value_map (term_type env value) ~default:[] ~f:(pattern_types env pattern)
      in
      let env = { env with var_types = types @ env.var_types } in
      formula
        (List.fold bindings ~init:env ~f:(fun env (id, v) -> bind env id (Value v)))
        body
  | Told _ -> unsupported at "This formula"

(** The formula [t], a sequence if it is a list literal and [expected] is a sequence type,
    as [[]] in [queue q []]. *)
and collection_application env ~at (module_name, function_name) args =
  let l = loc at in
  let* args = all args ~f:(fun t -> formula env t) in
  match (module_name, function_name, args) with
  | ("Finset" | "Set"), "empty", [] -> Ok (R.Expr.set ~loc:l [])
  | ("Finset" | "Set"), "singleton", [ x ] -> Ok (R.Expr.set ~loc:l [ x ])
  | ("Finset" | "Set"), "mem", [ x; s ] -> Ok (R.Expr.binary ~loc:l In x s)
  | ("Finset" | "Set"), "union", [ a; b ] -> Ok (R.Expr.binary ~loc:l Union a b)
  | ("Finset" | "Set"), "inter", [ a; b ] -> Ok (R.Expr.binary ~loc:l Inter a b)
  | ("Finset" | "Set"), "diff", [ a; b ] -> Ok (R.Expr.binary ~loc:l Diff a b)
  | ("Finset" | "Set"), "subset", [ a; b ] -> Ok (R.Expr.binary ~loc:l Subseteq a b)
  | "Finset", "choose", [ s ] -> Ok (R.Expr.call ~loc:l (name ~loc:l "choose") [ s ])
  | "Map", "const", [ v ] -> Ok (R.Expr.map_literal ~loc:l [] v)
  | "Map", "get", [ m; k ] -> Ok (R.Expr.index ~loc:l m k)
  | "Map", "set", [ m; k; v ] -> Ok (R.Expr.update ~loc:l m k v)
  | _ ->
      error at
        (Printf.sprintf "Unknown logical collection operation or wrong arity: %s.%s"
           module_name function_name)

and expected_formula env (expected : Types.type_expr option) (t : S.term) =
  let* () =
    match expected with
    | Some expected when opaque_module_types env ->
        Signature_contract.terms ~expected ~logical_types:env.data
          ~predicates:(fun q ->
            Option.map
              (List.Assoc.find env.ctx.preds (logical_key env q) ~equal:String.equal)
              ~f:snd)
          ~environment:env.ctx.env ~variables:env.var_types [ t ]
    | Some _ | None -> Ok ()
  in
  let literal = list_literal in
  let is_sequence ty =
    match Datatypes.desc env.data ty with
    | Tconstr (p, [ _ ], _) ->
        Option.exists (Datatypes.find env.data p) ~f:Datatypes.is_sequence
    | _ -> false
  in
  match (expected, literal t) with
  | Some ty, Some elements when is_sequence ty ->
      let* elements = all elements ~f:(formula env) in
      Ok (R.Expr.seq ~loc:(loc t.term_loc) elements)
  | Some expected, _
    when match spine t [] with
         | { term_desc = Tvar (Qid { pid_str = "to_sequence"; _ }); _ }, _ ->
             (not (List.Assoc.mem env.funcs "to_sequence" ~equal:String.equal))
             && not (List.Assoc.mem env.vars "to_sequence" ~equal:String.equal)
         | _ -> false ->
      let* () =
        Source.check_logical_expression ~is_list:(is_list_term env) env.ctx.env
          ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types ~expected t
      in
      let* value = formula env t in
      let* ty = typ env.ctx ~at:t.term_loc expected in
      Ok (R.Expr.annotated value ty)
  | _ -> formula env t

(** The OCaml type of [t], where it is known: a variable's, or a sequence's slice or
    concatenation. *)
and term_type env (t : S.term) =
  match (t.term_desc, spine (S.chain t) []) with
  | Tcast (_, ty), _ -> Result.ok (Source.ocaml_type env.ctx.env ~at:t.term_loc ty)
  | Tconst (Pconst_integer _), _ -> Some Predef.type_int
  | (Ttrue | Tfalse), _ -> Some Predef.type_bool
  | ( _,
      ( {
          term_desc =
            Tvar
              (Qid
                 {
                   pid_str =
                     ( "=" | "<>" | "==" | "!=" | "===" | "=/=" | "<" | ">" | "<=" | ">="
                     | "&&" | "||" | "/\\" | "\\/" );
                   _;
                 });
          _;
        },
        [ _; _ ] ) ) ->
      Some Predef.type_bool
  | ( _,
      ( { term_desc = Tvar (Qid { pid_str = "+" | "-" | "*" | "/" | "mod"; _ }); _ },
        [ a; b ] ) ) ->
      Option.first_some (term_type env a) (term_type env b)
  | Tcomprehension ((_, ty), _), _ ->
      Result.ok
        (Source.ocaml_type env.ctx.env ~at:t.term_loc
           (S.PTtyapp (Qid (S.mk_id ~loc:t.term_loc "set"), [ ty ])))
  | _, ({ term_desc = Tvar q; _ }, _) when Option.is_some (atomic_method env q) ->
      let signature, method_ = Option.value_exn (atomic_method env q) in
      Option.bind (atomic_inputs signature method_) ~f:(fun (_, outputs) ->
          List.hd outputs)
  | _, ({ term_desc = Tvar q; _ }, _) when Option.is_some (logical_signature env q) ->
      List.hd (Option.value_exn (logical_signature env q)).lemma_outputs
  | _, ({ term_desc = Tvar q; _ }, _ :: _) when Option.is_some (runtime_spec env q) ->
      Result.ok
        (Source.infer_logical_expression env.ctx.env
           ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types t)
  | _, ({ term_desc = Tvar (Qid { pid_str = "to_sequence"; _ }); _ }, [ _ ]) ->
      Result.ok
        (Source.infer_logical_expression ~is_list:(is_list_term env) env.ctx.env
           ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types t)
  | _, ({ term_desc = Tvar (Qid { pid_str = "length"; _ }); _ }, [ _ ]) ->
      Some Predef.type_int
  | ( _,
      ( {
          term_desc = Tvar (Qdot (Qid { pid_str = "List"; _ }, { pid_str = "length"; _ }));
          _;
        },
        [ _ ] ) ) ->
      Some Predef.type_int
  | Tvar (Qid { pid_str = x; _ }), _ ->
      List.Assoc.find env.var_types x ~equal:String.equal
  | _, ({ term_desc = Tvar (Qid { pid_str = "drop" | "take"; _ }); _ }, [ _; s ]) ->
      term_type env s
  | _, ({ term_desc = Tvar (Qid { pid_str = "++"; _ }); _ }, [ a; b ]) ->
      Option.first_some (term_type env a) (term_type env b)
  | Tfield (base, Qid { pid_str = f; _ }), _ ->
      let state =
        match base.term_desc with
        | Tvar (Qid id) ->
            Option.bind (state_fields env id.pid_str) ~f:(fun fields ->
                Option.map (List.Assoc.find fields f ~equal:String.equal) ~f:snd)
        | _ -> None
      in
      Option.first_some state
        (Option.bind (term_type env base) ~f:(fun ty ->
             let fallback =
               match Datatypes.desc env.data ty with
               | Tconstr (p, [ elt ], _) when Path.same p Predef.path_list ->
                   if String.equal f "hd" then Some elt
                   else if String.equal f "tl" then Some ty
                   else None
               | Tconstr (p, [], _) ->
                   Option.bind (Datatypes.find env.data p) ~f:(fun d ->
                       match d.ctors with
                       | [ c ] ->
                           Option.map
                             (List.Assoc.find
                                (List.zip_exn c.fields c.args)
                                f ~equal:String.equal)
                             ~f:(Datatypes.expand env.data)
                       | _ -> None)
               | _ -> None
             in
             Option.first_some (source_field_type env.ctx ty f) fallback))
  | _, ({ term_desc = Tvar (Qid { pid_str = "([])" | "last"; _ }); _ }, s :: _) ->
      (* An entry of a sequence. *)
      begin match Option.map (term_type env s) ~f:(Datatypes.desc env.data) with
      | Some (Tconstr (_, [ elt ], _)) -> Some elt
      | _ -> None
      end
  | _ -> None

and is_list_term env t =
  match Option.map (term_type env t) ~f:(Datatypes.desc env.data) with
  | Some (Tconstr (p, [ _ ], _)) -> Path.same p Predef.path_list
  | _ -> false

(** The OCaml type of the values that the location [t] holds, where it is known. *)
and location_type env (t : S.term) =
  match ghost_projection env t with
  | Some (field, _) -> Some field.field_value
  | None -> (
      match t.term_desc with
      | Tfield
          ({ term_desc = Tvar (Qid { pid_str = x; _ }); _ }, Qid { pid_str = label; _ })
        ->
          Option.bind (List.Assoc.find env.var_types x ~equal:String.equal) ~f:(fun ty ->
              field_type env.ctx ty label)
      | Tvar (Qid { pid_str = x; _ }) ->
          Option.bind (List.Assoc.find env.var_types x ~equal:String.equal) ~f:(fun ty ->
              field_type env.ctx ty "")
      | _ -> None)

and equality_term_type env (t : S.term) =
  match term_type env t with
  | Some ty -> Ok ty
  | None ->
      Source.infer_logical_expression env.ctx.env ~functions:(List.map env.funcs ~f:fst)
        ~variables:env.var_types t

(** Equality operands share a type, so a known operand supplies its context. *)
and equality_operand_types env a b =
  match (term_type env a, term_type env b) with
  | Some a, Some b -> Ok (a, b)
  | Some ty, None | None, Some ty -> Ok (ty, ty)
  | None, None ->
      begin match equality_term_type env a with
      | Ok ty -> Ok (ty, ty)
      | Error first ->
          begin match equality_term_type env b with
          | Ok ty -> Ok (ty, ty)
          | Error _ -> Error first
          end
      end

(** The application [t] of an operator or a constructor. *)
and application env (t : S.term) =
  let at = t.term_loc in
  let l = loc at in
  let head, args = spine t [] in
  match (head.term_desc, args) with
  | Tvar (Qid id), _ when List.Assoc.mem env.vars id.pid_str ~equal:String.equal ->
      error head.term_loc "A local proof value cannot be called as a logical function"
  | Tvar q, args when Option.is_some (atomic_method env q) ->
      let signature, method_ = Option.value_exn (atomic_method env q) in
      begin match (method_, atomic_inputs signature method_) with
      | ("pending" | "committed"), Some (inputs, _) ->
          let* values = typed_arguments env ~at inputs args in
          let values = atomic_arguments ~loc:l signature method_ values in
          let procedure = qualified_name ~loc:l signature.au_procedure in
          if String.equal method_ "pending" then Ok (R.Expr.au ~loc:l procedure values)
          else Ok (R.Expr.au_commit ~loc:l procedure values)
      | _ -> error at "An AU operation is only allowed in a proof expression"
      end
  | Tvar q, _
    when List.Assoc.mem env.ctx.proof_support.predicate_inputs (logical_key env q)
           ~equal:String.equal ->
      let key = logical_key env q in
      let raven, types = List.Assoc.find_exn env.ctx.preds key ~equal:String.equal in
      let* args = predicate_arguments env ~at ~display:(qualid_key q) key types args in
      Ok (R.Expr.call ~loc:l (qualified_name ~loc:l raven) args)
  | Tvar q, args when Option.is_some (logical_signature env q) ->
      logical_application env ~at (Option.value_exn (logical_signature env q)) args
  | Tvar q, args when Option.is_some (runtime_spec env q) ->
      let* args = all args ~f:(formula env) in
      Ok
        (R.Expr.call ~loc:l
           (Qualified_name.raven ~loc:l (Option.value_exn (runtime_spec env q)))
           args)
  | Tvar (Qdot (parent, _) as q), _ when Option.is_some (resource_module env parent) ->
      error at ("Unknown proof module member " ^ qualid_key q)
  | Tvar q, args when Option.is_some (collection_builtin env q) ->
      collection_application env ~at (Option.value_exn (collection_builtin env q)) args
  | Tvar (Qid { pid_str = "not"; _ }), [ a ] ->
      let* a = formula env a in
      Ok (R.Expr.not_ ~loc:l a)
  | Tvar (Qid { pid_str = "own"; _ }), ([ location; v ] | [ location; v; _ ]) ->
      let expected = location_type env location in
      let* () =
        match (ghost_projection env location, expected) with
        | Some _, Some expected ->
            Source.check_logical_expression env.ctx.env
              ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types ~expected v
        | _ -> Ok ()
      in
      let* location = location_of env location in
      let* v = expected_formula env expected v in
      let* fraction =
        match args with
        | [ _; _; fraction ] ->
            let* () =
              match ghost_projection env (List.hd_exn args) with
              | Some (field, _) when resource_field env field ->
                  error at "Resource fields do not take a fractional permission"
              | _ -> Ok ()
            in
            let* permission_type =
              Source.ocaml_type env.ctx.env ~at
                (S.PTtyapp
                   (Qdot (Qid (S.mk_id ~loc:at "Permission"), S.mk_id ~loc:at "t"), []))
            in
            let* () =
              Source.check_logical_expression env.ctx.env
                ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types
                ~expected:permission_type fraction
            in
            let* fraction = formula env fraction in
            Ok [ fraction ]
        | _ -> Ok []
      in
      Ok (R.Expr.own ~loc:l ([ location; v ] @ fraction))
  | Tvar (Qid { pid_str = "([])"; _ }), [ s; i ] ->
      let* s = formula env s in
      let* i = formula env i in
      Ok (R.Expr.index ~loc:l s i)
  | Tvar (Qid { pid_str = "++"; pid_fixity = Infix; _ }), [ a; b ] ->
      (* Concatenating sequences, as list literals are here. *)
      let operand (t : S.term) =
        match list_literal t with
        | Some elements ->
            let* elements = all elements ~f:(formula env) in
            Ok (R.Expr.seq ~loc:(loc t.term_loc) elements)
        | None -> formula env t
      in
      let* a = operand a in
      let* b = operand b in
      Ok (R.Expr.call ~loc:l (R.Name.make ~loc:l "++") [ a; b ])
  | Tvar (Qid { pid_str = "-"; pid_fixity = Prefix; _ }), [ a ] ->
      let* a = formula env a in
      Ok (R.Expr.neg ~loc:l a)
  | Tvar (Qid { pid_str = "@"; pid_fixity = Infix; _ }), [ a; b ] ->
      let* a = formula env a in
      let* b = formula env b in
      Ok (R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ "List" ] "++") [ a; b ])
  | Tvar (Qid ({ pid_str = operator; pid_fixity = Infix; _ } as id)), [ a; b ] ->
      begin match spec_binop operator with
      | None -> unsupported at (Printf.sprintf "The operator %s" operator)
      | Some op -> (
          let* () =
            match operator with
            | "===" | "=/=" ->
                begin match (term_type env a, term_type env b) with
                | Some left, Some right
                  when not (Ctype.is_equal env.ctx.env false [ left ] [ right ]) ->
                    error id.pid_loc
                      "Logical equality requires operands of the same OCaml type"
                | _ -> Ok ()
                end
            | ("=" | "<>") when not (nullary_constructor a || nullary_constructor b) ->
                let* a_type, b_type = equality_operand_types env a b in
                if
                  spec_contains_runtime_refs env.ctx a_type
                  || spec_contains_runtime_refs env.ctx b_type
                then
                  let direct =
                    Datatypes.is_heap_ref env.ctx.types a_type
                    || Datatypes.is_heap_ref env.ctx.types b_type
                  in
                  error id.pid_loc
                    (if direct then
                       "Structural equality on references is unsupported; use == or != \
                        for reference identity"
                     else
                       "Structural equality on values containing references is \
                        unsupported")
                else Ok ()
            | "==" | "!=" ->
                if nullary_constructor a || nullary_constructor b then Ok ()
                else
                  let* a_type = equality_term_type env a in
                  let* b_type = equality_term_type env b in
                  if mathematical_type env.ctx a_type || mathematical_type env.ctx b_type
                  then
                    error id.pid_loc
                      "Physical equality on logical values is unsupported; use = or <>"
                  else if
                    Datatypes.immediate env.ctx.types a_type
                    || Datatypes.immediate env.ctx.types b_type
                  then Ok ()
                  else
                    error id.pid_loc
                      "Physical equality on boxed values is unsupported in specifications"
            | _ -> Ok ()
          in
          (* A literal compared with a sequence is one. *)
          let a_type = term_type env a and b_type = term_type env b in
          let* a = expected_formula env b_type a in
          let* b = expected_formula env a_type b in
          match op with
          | Div -> Ok (prelude_call ~loc:l Prelude.div [ a; b ])
          | Mod -> Ok (prelude_call ~loc:l Prelude.mod_ [ a; b ])
          | _ -> Ok (R.Expr.binary ~loc:l op a b))
      end
  | Tvar (Qid { pid_str = c; _ }), _ when is_constructor c -> constructor env t args
  | Tvar (Qdot (_, id)), _ when is_constructor id.pid_str -> constructor env t args
  | Tvar q, _ :: _
    when List.Assoc.mem env.funcs (logical_key env q) ~equal:String.equal
         && not
              (List.exists env.ctx.proof_support.runtime_functions.entries
                 ~f:(fun (_, target) ->
                   String.equal
                     (Qualified_name.to_string target)
                     (List.Assoc.find_exn env.funcs (logical_key env q)
                        ~equal:String.equal))) ->
      let f = logical_key env q in
      (* A predicate's arguments have its parameters' types. *)
      let expected =
        match List.Assoc.find env.ctx.preds f ~equal:String.equal with
        | Some (_, types) when List.length types = List.length args ->
            List.map types ~f:Option.some
        | _ -> List.map args ~f:(fun _ -> None)
      in
      let* args =
        all (List.zip_exn expected args) ~f:(fun (expected, a) ->
            expected_formula env expected a)
      in
      let func = List.Assoc.find_exn env.funcs f ~equal:String.equal in
      Ok (R.Expr.call ~loc:l (qualified_name ~loc:l func) args)
  | Tvar (Qid { pid_str = "to_sequence"; _ }), args ->
      if List.length args <> 1 then error at "to_sequence expects a list"
      else
        let* _ =
          Source.infer_logical_expression ~is_list:(is_list_term env) env.ctx.env
            ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types t
        in
        let* args = all args ~f:(formula env) in
        Ok (R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ "Seq" ] "of_list") args)
  | Tvar (Qid { pid_str = ("length" | "last" | "drop" | "take") as f; _ }), args -> begin
      let* args = all args ~f:(formula env) in
      let length s =
        R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ "Seq" ] "length") [ s ]
      in
      match (f, args) with
      | "length", [ s ] -> Ok (length s)
      | "last", [ s ] ->
          Ok
            (R.Expr.index ~loc:l s
               (R.Expr.binary ~loc:l Minus (length s) (R.Expr.int ~loc:l 1)))
      | "drop", [ n; s ] -> Ok (R.Expr.slice_from ~loc:l s n)
      | "take", [ n; s ] -> Ok (R.Expr.slice_to ~loc:l s n)
      | _ ->
          error at
            (Printf.sprintf "%s expects %s" f
               (if String.equal f "drop" || String.equal f "take" then
                  "a length and a sequence"
                else "a sequence"))
    end
  | Tvar q, args when Option.is_some (list_function q) ->
      let* args = all args ~f:(formula env) in
      let f = Option.value_exn (list_function q) in
      Ok (R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ "List" ] f) args)
  | _ -> unsupported at "A call of a function in a contract"

and typed_arguments env ~at inputs args =
  let is_list = is_list_term env in
  if List.length args <> List.length inputs then
    error at (Printf.sprintf "Expected %d arguments" (List.length inputs))
  else
    all (List.zip_exn inputs args) ~f:(fun (ty, value) ->
        let sequence =
          match Datatypes.desc env.data ty with
          | Tconstr (path, [ _ ], _) ->
              Option.exists (Datatypes.find env.data path) ~f:Datatypes.is_sequence
          | _ -> false
        in
        let* () =
          if sequence then
            Signature_contract.terms ~expected:ty ~logical_types:env.data
              ~predicates:(fun q ->
                Option.map
                  (List.Assoc.find env.ctx.preds (logical_key env q) ~equal:String.equal)
                  ~f:snd)
              ~environment:env.ctx.env ~variables:env.var_types [ value ]
          else
            Source.check_logical_expression ~is_list env.ctx.env
              ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types ~expected:ty
              value
        in
        let* () =
          match term_type env value with
          | Some actual
            when (not sequence)
                 && not (Ctype.is_equal env.ctx.env false [ ty ] [ actual ]) ->
              error value.term_loc
                (Stdlib.Format.asprintf "Expected logical type %a but found %a"
                   Printtyp.type_expr ty Printtyp.type_expr actual)
          | _ -> Ok ()
        in
        let* value = expected_formula env (Some ty) value in
        let* raven_type = typ env.ctx ~at ty in
        Ok (R.Expr.annotated value raven_type))

and predicate_arguments env ~at ?display key types args =
  match
    List.Assoc.find env.ctx.proof_support.predicate_inputs key ~equal:String.equal
  with
  | None ->
      if List.length types = List.length args then
        all (List.zip_exn types args) ~f:(fun (ty, value) ->
            expected_formula env (Some ty) value)
      else all args ~f:(formula env)
  | Some minimum ->
      let maximum = List.length types and arity = List.length args in
      if arity < minimum || arity > maximum then
        error at
          (Printf.sprintf "Predicate %s expects between %d and %d arguments"
             (Option.value display ~default:key)
             minimum maximum)
      else typed_arguments env ~at (List.take types arity) args

and logical_application env ~at signature args =
  let l = loc at in
  let* () =
    if List.length args = List.length signature.lemma_inputs then Ok ()
    else
      error at
        (Printf.sprintf "%s expects %d arguments" signature.lemma_raven
           (List.length signature.lemma_inputs))
  in
  let* args = typed_arguments env ~at signature.lemma_inputs args in
  let n = qualified_name ~loc:l signature.lemma_raven in
  if signature.lemma_constant then Ok (R.Expr.var ~loc:l n)
  else Ok (R.Expr.call ~loc:l n args)

(** The OCaml types of the names that the pattern [p] binds, matching a value of type [t].
*)
and pattern_types env (p : S.pat) (t : Types.type_expr) : (string * Types.type_expr) list
    =
  match (p.pat_desc, Datatypes.desc env.data t) with
  | Pid id, _ -> [ (id.pid_str, t) ]
  | Pcast (p, _), _ -> pattern_types env p t
  | Ptuple ps, Ttuple ts when List.length ps = List.length ts ->
      List.concat_map (List.zip_exn ps ts) ~f:(fun (p, (_, t)) -> pattern_types env p t)
  | Pconstr (q, arg), Tconstr (path, args, _) -> begin
      let c = match q with Qid id | Qdot (_, id) -> id.pid_str in
      let arg_types =
        match (c, args) with
        | "::", [ elt ] when Path.same path Predef.path_list -> [ elt; t ]
        | "Some", [ elt ] when Path.same path Predef.path_option -> [ elt ]
        | _ ->
            begin match find_constructor env q with
            | Some (d, ctor) when Datatypes.declares d path -> ctor.args
            | Some _ | None ->
                begin match Datatypes.find env.data path with
                | Some d ->
                    Option.value_map
                      (List.find d.ctors ~f:(fun ctor -> String.equal ctor.ocaml c))
                      ~default:[]
                      ~f:(fun ctor -> ctor.args)
                | None -> []
                end
            end
      in
      let arg_patterns =
        match (arg, arg_types) with
        | None, _ | _, [] -> []
        | Some p, [ _ ] -> [ p ]
        | Some { pat_desc = Ptuple ps; _ }, _ -> ps
        | Some _, _ -> []
      in
      if List.length arg_patterns <> List.length arg_types then []
      else
        List.concat_map (List.zip_exn arg_patterns arg_types) ~f:(fun (p, t) ->
            pattern_types env p t)
    end
  | _ -> []

(** The formula [t], with the names free in it that can be typed existentially quantified,
    as [n] in [own x.next n && lseg n t]. *)
and quantified env (t : S.term) =
  let l = loc t.term_loc in
  let* free = free_typed ~lenient:true env [ t ] ~at:t.term_loc in
  let env =
    List.fold free ~init:env ~f:(fun env (x, raven, ty, _, _) ->
        { (bind env x (Raven raven)) with var_types = (x, ty) :: env.var_types })
  in
  let* body = formula env t in
  match free with
  | [] -> Ok body
  | _ ->
      let vars =
        List.map free ~f:(fun (_, raven, _, typ, l) ->
            R.Var.make ~loc:l (ident ~loc:l raven) typ)
      in
      Ok (R.Expr.exists ~loc:l vars body)

(** The location [t], as in [own r.count n]: a field of a variable of known type. *)
and location_of env (t : S.term) =
  let at = t.term_loc in
  let l = loc at in
  let* () =
    let owner = match t.term_desc with Tfield (owner, _) -> owner | _ -> t in
    match term_type env owner with
    | Some typ -> (
        match Types.get_desc (Ctype.expand_head env.ctx.env typ) with
        | Tconstr (path, _, _) when opaque_module_path env path ->
            error at
              "Ownership of an abstract module type must be exposed through a predicate"
        | _ -> Ok ())
    | None -> Ok ()
  in
  match ghost_projection env t with
  | Some (field, owner) ->
      let* () =
        match term_type env owner with
        | None -> Ok ()
        | Some actual
          when Ctype.is_equal env.ctx.env false [ field.field_owner ] [ actual ] ->
            Ok ()
        | Some _ -> error owner.term_loc "This ghost field has a different owner type"
      in
      let* () =
        Source.check_logical_expression env.ctx.env ~functions:(List.map env.funcs ~f:fst)
          ~variables:env.var_types ~expected:field.field_owner owner
      in
      let* owner = formula env owner in
      Ok (R.Expr.field ~loc:l owner (qualified_name ~loc:l (ghost_field_name field)))
  | None -> (
      let* () =
        match spine t [] with
        | ( { term_desc = Tvar (Qdot (Qid m, operation)); _ },
            [ { term_desc = Tvar field; _ }; _ ] )
          when String.equal m.pid_str "Ghost" && String.equal operation.pid_str "at" ->
            error (S.qualid_loc field) "Unknown or inaccessible ghost field"
        | _ -> Ok ()
      in
      match t.term_desc with
      | Tfield
          ({ term_desc = Tvar (Qid { pid_str = x; _ }); _ }, Qid { pid_str = label; _ })
        -> begin
          let* r = formula env { t with term_desc = Tvar (Qid (S.mk_id ~loc:at x)) } in
          match List.Assoc.find env.var_types x ~equal:String.equal with
          | None -> error at (Printf.sprintf "The type of %s is not known here" x)
          | Some typ -> begin
              let* field = field_of_type env.ctx ~at typ label in
              match (field, atomic_in_record env.ctx typ label) with
              | Some field, _ -> Ok (R.Expr.field ~loc:l r (qualified_name ~loc:l field))
              | None, Some atomic -> begin
                  (* An atomic that an immutable record holds. *)
                  let atomic_ref = R.Expr.field ~loc:l r (qualified_name ~loc:l label) in
                  let* field = field_of_type env.ctx ~at atomic "" in
                  match field with
                  | Some field ->
                      Ok (R.Expr.field ~loc:l atomic_ref (qualified_name ~loc:l field))
                  | None -> error at (Printf.sprintf "%s has no mutable field %s" x label)
                end
              | None, None ->
                  error at (Printf.sprintf "%s has no mutable field %s" x label)
            end
        end
      | Tvar (Qid { pid_str = x; _ }) -> begin
          let* r = formula env t in
          let* field =
            match List.Assoc.find env.var_types x ~equal:String.equal with
            | None -> error at (Printf.sprintf "The type of %s is not known here" x)
            | Some typ -> field_of_type env.ctx ~at typ ""
          in
          match field with
          | Some field -> Ok (R.Expr.field ~loc:l r (qualified_name ~loc:l field))
          | None ->
              error at (Printf.sprintf "%s is not an atomic, as owned without a field" x)
        end
      | _ -> begin
          (* An atomic given by an expression, as [last s.cells]. *)
          let* field =
            match term_type env t with
            | Some typ -> field_of_type env.ctx ~at typ ""
            | None -> Ok None
          in
          match field with
          | Some field ->
              let* r = formula env t in
              Ok (R.Expr.field ~loc:l r (qualified_name ~loc:l field))
          | None ->
              unsupported at
                "This location, other than a field of a variable or an atomic,"
        end)

(** The constructor [t], or the application [t] of a constructor to [args]. *)
and constructor env (t : S.term) args =
  let at = t.term_loc in
  let l = loc at in
  let head, _ = spine t [] in
  let q = match head.term_desc with Tvar q -> q | _ -> Qid (S.mk_id ~loc:at "") in
  let c_name = qualid_key q in
  match find_constructor env q with
  | None -> error head.term_loc (Printf.sprintf "Unbound constructor %s" c_name)
  | Some (d, c) ->
      let tuple (a : S.term) =
        match a.term_desc with Ttuple ts -> Some ts | _ -> None
      in
      let* args = ctor_args ~at (List.length c.fields) args ~tuple in
      let* args = all args ~f:(formula env) in
      Ok (R.Expr.call ~loc:l (Datatypes.ctor_name ~loc:l d c) args)

(** The condition under which the value [v] matches the pattern [p] of a contract, [None]
    if it always does, and the names [p] binds, with their values. *)
and spec_pattern env (p : S.pat) (v : R.Expr.t) =
  let at = p.pat_loc in
  let l = loc at in
  let conjoin conds =
    List.reduce (List.filter_opt conds) ~f:(fun a b -> R.Expr.binary ~loc:l And a b)
  in
  let components ps values =
    let* matched = all (List.zip_exn ps values) ~f:(fun (p, v) -> spec_pattern env p v) in
    Ok (List.map matched ~f:fst, List.concat_map matched ~f:snd)
  in
  match p.pat_desc with
  | Pwild -> Ok (None, [])
  | Pid id -> Ok (None, [ (id.pid_str, v) ])
  | Pcast (p, _) -> spec_pattern env p v
  | Pconst (Pconst_integer (n, None)) ->
      Ok (Some (R.Expr.binary ~loc:l Eq v (R.Expr.int ~loc:l (Int.of_string n))), [])
  | Pconst _ -> unsupported at "This constant"
  | Ptuple ps ->
      let* conds, binds =
        components ps (List.mapi ps ~f:(fun i _ -> R.Expr.tuple_get ~loc:l v i))
      in
      Ok (conjoin conds, binds)
  | Pconstr (Qid { pid_str = ("true" | "false") as b; _ }, None) ->
      Ok
        (Some (R.Expr.binary ~loc:l Eq v (R.Expr.bool ~loc:l (String.equal b "true"))), [])
  | Pconstr (Qid { pid_str = "()"; _ }, None) -> Ok (None, [])
  | Pconstr (q, arg) ->
      let c_name = qualid_key q in
      begin match find_constructor env q with
      | None -> error at (Printf.sprintf "Unbound constructor %s" c_name)
      | Some (_, c) ->
          let tuple (p : S.pat) =
            match p.pat_desc with Ptuple ps -> Some ps | _ -> None
          in
          let* args = ctor_args ~at (List.length c.fields) (Option.to_list arg) ~tuple in
          let fields =
            List.map c.fields ~f:(fun f ->
                R.Expr.field ~loc:l v (qualified_name ~loc:l f))
          in
          let* conds, binds = components args fields in
          Ok (conjoin (Some (R.Expr.is_ ~loc:l v (ident ~loc:l c.raven)) :: conds), binds)
      end

(** A match on the value [v] in a contract: a Raven match if the cases are flat, and
    otherwise conditional expressions, whose last case is not tested. *)
and spec_match env ~at ?scrutinee_type v (cases : (S.pat * S.term) list) =
  let l = loc at in
  (* The environment of a case's body, with the types of its pattern's variables. *)
  let typed env (p : S.pat) =
    let types =
      Option.value_map scrutinee_type ~default:[] ~f:(fun t -> pattern_types env p t)
    in
    { env with var_types = types @ env.var_types }
  in
  let flat_arg (p : S.pat) =
    match p.pat_desc with Pwild -> Some None | Pid id -> Some (Some id) | _ -> None
  in
  let rec flat seen = function
    | [] -> Some []
    | [ ((p : S.pat), body) ] when Option.is_some (flat_arg p) ->
        Some [ (`Any (Option.join (flat_arg p)), (p, body)) ]
    | ((p : S.pat), body) :: rest ->
        begin match p.pat_desc with
        | Pconstr (q, arg) -> begin
            let args =
              match arg with
              | None -> Some []
              | Some { pat_desc = Ptuple ps; _ } -> Option.all (List.map ps ~f:flat_arg)
              | Some p -> Option.map (flat_arg p) ~f:(fun a -> [ a ])
            in
            match (find_constructor env q, args) with
            | Some (_, c), Some args
              when List.length args = List.length c.fields
                   && not (List.mem seen c.raven ~equal:String.equal) ->
                Option.map
                  (flat (c.raven :: seen) rest)
                  ~f:(fun rest -> (`Ctor (c, args), (p, body)) :: rest)
            | _ -> None
          end
        | _ -> None
        end
  in
  match flat [] cases with
  | Some flat ->
      let case = function
        | `Any id, (p, body) ->
            let env =
              Option.value_map id ~default:env ~f:(fun id ->
                  bind env id.S.pid_str (Value v))
            in
            let* body = quantified (typed env p) body in
            Ok (R.Expr.Default, body)
        | `Ctor ((c : Datatypes.ctor), args), (p, body) ->
            if env.logical_definition then begin
              let* _, bindings = spec_pattern env p v in
              let env =
                List.fold bindings ~init:env ~f:(fun env (x, value) ->
                    bind env x (Value value))
              in
              let* body = quantified (typed env p) body in
              Ok
                ( R.Expr.Case
                    (ident ~loc:l c.raven, List.map args ~f:(fun _ -> ident ~loc:l "_")),
                  body )
            end
            else begin
              let var = function
                | None -> ident ~loc:l "_"
                | Some (id : S.id) -> ident ~loc:(loc id.pid_loc) id.pid_str
              in
              let env =
                List.fold args ~init:env ~f:(fun env -> function
                  | None -> env
                  | Some (id : S.id) -> bind env id.pid_str (Raven id.pid_str))
              in
              let* body = quantified (typed env p) body in
              Ok (R.Expr.Case (ident ~loc:l c.raven, List.map args ~f:var), body)
            end
      in
      let* cases = all flat ~f:case in
      Ok (R.Expr.match_ ~loc:l v cases)
  | None ->
      let case_body p binds body =
        quantified
          (List.fold binds ~init:(typed env p) ~f:(fun env (x, value) ->
               bind env x (Value value)))
          body
      in
      let rec chain = function
        | [] -> error at "A match needs at least one case"
        | [ (p, body) ] ->
            let* _, binds = spec_pattern env p v in
            case_body p binds body
        | (p, body) :: rest -> begin
            let* cond, binds = spec_pattern env p v in
            let* body = case_body p binds body in
            match cond with
            | None -> Ok body
            | Some cond ->
                let* rest = chain rest in
                Ok (R.Expr.ite ~loc:l cond body rest)
          end
      in
      chain cases

(** The latest binding of each variable in scope. *)
let scope ctx =
  List.fold (List.rev ctx.names.scope) ~init:[] ~f:(fun acc (x, b) ->
      (x, b) :: List.Assoc.remove acc x ~equal:String.equal)

(** The environment of a contract term written in code, as an invariant, with the
    variables in scope. *)
let scope_env ctx =
  let scope = scope ctx in
  {
    ctx;
    var_types =
      List.filter_map scope ~f:(fun (x, (_, t)) -> Option.map t ~f:(fun t -> (x, t)));
    logical_definition = false;
    data = ctx.types;
    funcs = ctx.spec_funcs;
    vars = List.map scope ~f:(fun (x, (raven, _)) -> (x, Raven raven));
  }

(** A call of a checked proof lemma, separate from logical function applications. *)
let lemma_call env (t : S.term) =
  let head, args = spine t [] in
  match head.term_desc with
  | Tvar (Qid id) when List.Assoc.mem env.vars id.pid_str ~equal:String.equal ->
      error id.pid_loc "A local proof value cannot be called as a lemma"
  | Tvar q ->
      let display = qualid_key q in
      begin match
        List.Assoc.find env.ctx.proof_lemmas (logical_key env q) ~equal:String.equal
      with
      | None -> error head.term_loc (Printf.sprintf "Unknown lemma %s" display)
      | Some signature ->
          let maximum = List.length signature.lemma_inputs in
          let minimum = maximum - signature.lemma_implicit_count in
          let arity = List.length args in
          if arity < minimum || arity > maximum then
            error t.term_loc
              (if minimum = maximum then
                 Printf.sprintf "Lemma %s expects %d arguments" display maximum
               else
                 Printf.sprintf "Lemma %s expects between %d and %d arguments" display
                   minimum maximum)
          else
            let* args =
              typed_arguments env ~at:t.term_loc
                (List.take signature.lemma_inputs arity)
                args
            in
            Ok
              ( R.Expr.call ~loc:(loc t.term_loc)
                  (qualified_name ~loc:(loc t.term_loc) signature.lemma_raven)
                  args,
                signature.lemma_outputs )
      end
  | _ -> error t.term_loc "Expected a lemma applied to its arguments"

let predicate_use env ~unfold t witnesses make =
  let head, args = spine t [] in
  match head.term_desc with
  | Tvar q when List.Assoc.mem env.ctx.preds (logical_key env q) ~equal:String.equal ->
      let key = logical_key env q in
      let* () =
        if List.mem env.ctx.proof_support.opaque_predicates key ~equal:String.equal then
          error head.term_loc
            "The definition of this predicate is hidden by its module signature"
        else Ok ()
      in
      let raven, types = List.Assoc.find_exn env.ctx.preds key ~equal:String.equal in
      let* args =
        predicate_arguments env ~at:t.term_loc ~display:(qualid_key q) key types args
      in
      let* witnesses =
        all witnesses ~f:(fun (id, t) ->
            if unfold then
              match
                (List.Assoc.find env.vars id.S.pid_str ~equal:String.equal, t.S.term_desc)
              with
              | Some (Raven target), Tvar (Qid existential) ->
                  Ok
                    ( ident ~loc:(loc id.pid_loc) target,
                      R.Expr.var ~loc:(loc existential.pid_loc)
                        (name ~loc:(loc existential.pid_loc) existential.pid_str) )
              | None, _ ->
                  error id.pid_loc (Printf.sprintf "Unbound proof variable %s" id.pid_str)
              | _ -> error t.term_loc "An unfold binding names an existential variable"
            else
              let* value = formula env t in
              Ok (ident ~loc:(loc id.pid_loc) id.pid_str, value))
      in
      let l = loc t.S.term_loc in
      Ok (make ~loc:l ?witnesses:(Some witnesses) (qualified_name ~loc:l raven) args)
  | _ -> error t.term_loc "Expected a predicate applied to its arguments"

(** Ghost annotations invoke checked proof operations. *)
let proof_statement env = function
  | S.Fold t -> predicate_use env ~unfold:false t [] R.Stmt.fold
  | Unfold t -> predicate_use env ~unfold:true t [] R.Stmt.unfold
  | Fold_with (t, ws) -> predicate_use env ~unfold:false t ws R.Stmt.fold
  | Unfold_with (t, ws) -> predicate_use env ~unfold:true t ws R.Stmt.unfold
  | Assert t ->
      let* value = formula env t in
      Ok (R.Stmt.assert_ ~loc:(loc t.term_loc) (R.Spec.make value))
  | Ghost_call t ->
      let* call, outputs = lemma_call env t in
      if not (List.is_empty outputs) then
        error t.term_loc "Bind all the results of this lemma"
      else Ok (R.Stmt.call ~loc:(loc t.term_loc) call)

type proof_target = { target_name : string; target_type : Types.type_expr }

let atomic_proof_signature env t =
  let head, _ = spine t [] in
  match head.S.term_desc with
  | Tvar q ->
      Option.bind (atomic_method env q) ~f:(fun (signature, method_) ->
          if List.mem [ "bind"; "access"; "abort"; "commit" ] method_ ~equal:String.equal
          then
            Option.map (atomic_inputs signature method_) ~f:(fun (inputs, outputs) ->
                {
                  lemma_raven = qualid_key q;
                  lemma_constant = false;
                  lemma_inputs = inputs;
                  lemma_implicit_count = 0;
                  lemma_outputs = outputs;
                })
          else None)
  | _ -> None

let proof_call env t =
  let head, args = spine t [] in
  match head.S.term_desc with
  | Tvar q when Option.is_some (atomic_proof_signature env t) ->
      let signature, method_ = Option.value_exn (atomic_method env q) in
      let inputs, outputs = Option.value_exn (atomic_inputs signature method_) in
      let* values = typed_arguments env ~at:t.term_loc inputs args in
      let* () =
        if
          String.equal method_ "bind"
          && not
               (Option.equal String.equal env.ctx.current_procedure
                  (Some signature.au_procedure))
        then error t.term_loc "An AU token can only be bound in its own procedure"
        else Ok ()
      in
      let l = loc t.term_loc in
      let values =
        if String.equal method_ "bind" then []
        else atomic_arguments ~loc:l signature method_ values
      in
      let method_ =
        match method_ with
        | "bind" -> "bindAU"
        | "access" -> "openAU"
        | "abort" -> "abortAU"
        | "commit" -> "commitAU"
        | _ -> method_
      in
      Ok (R.Expr.call ~loc:l (name ~loc:l method_) values, outputs)
  | _ -> lemma_call env t

let proof_signature env (t : S.term) =
  let head, _ = spine t [] in
  match atomic_proof_signature env t with
  | Some _ as signature -> signature
  | None ->
      begin match head.term_desc with
      | Tvar (Qid id) when List.Assoc.mem env.vars id.pid_str ~equal:String.equal -> None
      | Tvar q ->
          List.Assoc.find env.ctx.proof_lemmas (logical_key env q) ~equal:String.equal
      | _ -> None
      end

let ghost_fpu env t =
  let _, args = spine t [] in
  match args with
  | [ location; before; after ] ->
      begin match ghost_projection env location with
      | None -> error location.term_loc "Ghost.fpu needs a declared ghost field location"
      | Some (field, _) ->
          let* () =
            if resource_field env field then Ok ()
            else error t.term_loc "Ghost.fpu requires a resource field"
          in
          let* location = location_of env location in
          let value t =
            let* () =
              match term_type env t with
              | Some actual
                when not
                       (Ctype.is_equal env.ctx.env false [ field.field_value ] [ actual ])
                ->
                  error t.S.term_loc "This update uses a different resource type"
              | _ -> Ok ()
            in
            expected_formula env (Some field.field_value) t
          in
          let* before = value before in
          let* after = value after in
          let l = loc t.S.term_loc in
          Ok
            (R.Stmt.call ~loc:l
               (R.Expr.call ~loc:l (name ~loc:l "fpu") [ location; before; after ]))
      end
  | _ -> error t.term_loc "Ghost.fpu expects a location and two resources"

(** Initializers are attached only to fresh allocations. *)
let ghost_initializers env ~owner t =
  let* entries =
    match list_literal t with
    | Some entries -> Ok entries
    | None -> error t.S.term_loc "Ghost initializers must be a list literal"
  in
  let* fields =
    all entries ~f:(fun entry ->
        match spine entry [] with
        | { term_desc = Tvar (Qdot (Qid m, op)); _ }, [ { term_desc = Tvar q; _ }; value ]
          when String.equal m.pid_str "Ghost" && String.equal op.pid_str "init" ->
            let at = S.qualid_loc q in
            begin match ghost_descriptor env q with
            | None -> error at "Unknown ghost field"
            | Some _ when shadowed_ghost_descriptor env q ->
                error at "This name shadows a ghost field descriptor"
            | Some field ->
                let* () =
                  if Ctype.is_equal env.ctx.env false [ owner ] [ field.field_owner ] then
                    Ok ()
                  else error at "This ghost field has a different owner type"
                in
                let* () =
                  Source.check_logical_expression env.ctx.env
                    ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types
                    ~expected:field.field_value value
                in
                let* value = expected_formula env (Some field.field_value) value in
                Ok
                  ( ghost_field_name field,
                    ( qualified_name ~loc:(loc entry.term_loc) (ghost_field_name field),
                      Some value ) )
            end
        | _ -> error entry.term_loc "Expected Ghost.init field value")
  in
  let* () =
    match List.find_a_dup (List.map fields ~f:fst) ~compare:String.compare with
    | None -> Ok ()
    | Some _ -> error t.term_loc "A ghost field is initialized more than once"
  in
  Ok (List.map fields ~f:snd)

let ghost_value_location env t =
  match ghost_projection env t with
  | None -> error t.S.term_loc "Expected a declared ghost field location"
  | Some (field, _) when resource_field env field ->
      error t.term_loc "Ghost.read and Ghost.write require an ordinary value field"
  | Some (field, _) ->
      let* location = location_of env t in
      Ok (field, location)

(** Type information for lexical bindings; annotations resolve logical operations whose
    OCaml result type is not available. Raven checks every generated assignment. *)
let rec proof_value_types env (t : S.term) =
  match proof_signature env t with
  | Some signature -> Ok (List.map signature.lemma_outputs ~f:Option.some)
  | None ->
      begin match t.term_desc with
      | Ttuple ts ->
          let* ts = all ts ~f:(proof_value_type env) in
          Ok ts
      | _ ->
          let* ty = proof_value_type env t in
          Ok [ ty ]
      end

and proof_value_type env (t : S.term) =
  match (ghost_operation t, snd (spine t [])) with
  | Some "alloc", [ _ ] ->
      Result.map (Source.ghost_type env.ctx.env ~at:t.term_loc) ~f:Option.some
  | Some "read", [ location ] ->
      let* field, _ = ghost_value_location env location in
      Ok (Some field.field_value)
  | _ -> (
      match t.term_desc with
      | Tcast (_, ty) ->
          let* ty = Source.ocaml_type env.ctx.env ~at:t.term_loc ty in
          Ok (Some ty)
      | Tconst (Pconst_integer _) -> Ok (Some Predef.type_int)
      | Ttrue | Tfalse -> Ok (Some Predef.type_bool)
      | Tapply ({ term_desc = Tvar (Qid { pid_str = "Some"; _ }); _ }, value) ->
          let* ty = proof_value_type env value in
          Ok (Option.map ty ~f:(fun ty -> Ctype.newconstr Predef.path_option [ ty ]))
      | Ttuple [] -> Ok (Some Predef.type_unit)
      | Ttuple ts ->
          let* ts = all ts ~f:(proof_value_type env) in
          Ok
            (Option.map (Option.all ts) ~f:(fun ts ->
                 Btype.newgenty (Ttuple (List.map ts ~f:(fun ty -> (None, ty))))))
      | _ -> (
          match term_type env t with
          | Some ty -> Ok (Some ty)
          | None ->
              Result.map
                (Source.infer_logical_expression env.ctx.env
                   ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types t)
                ~f:Option.some))

let proof_pattern_parts (p : S.pat) = match p.pat_desc with Ptuple ps -> ps | _ -> [ p ]

let proof_binding_types env pattern inferred =
  let parts = proof_pattern_parts pattern in
  let inferred =
    match (parts, inferred) with
    | [ _ ], Some [] -> Some [ Some Predef.type_unit ]
    | [ _ ], Some (_ :: _ :: _ as ts) ->
        Some
          [
            Option.map (Option.all ts) ~f:(fun ts ->
                Btype.newgenty (Ttuple (List.map ts ~f:(fun ty -> (None, ty)))));
          ]
    | _ :: _ :: _, Some [ Some ty ] ->
        begin match Datatypes.desc env.data ty with
        | Ttuple ts -> Some (List.map ts ~f:(fun (_, ty) -> Some ty))
        | _ -> inferred
        end
    | _ -> inferred
  in
  let* () =
    match inferred with
    | Some ts when List.length ts <> List.length parts ->
        error pattern.S.pat_loc "The binding pattern does not match the proof results"
    | _ -> Ok ()
  in
  let inferred = Option.value inferred ~default:(List.map parts ~f:(fun _ -> None)) in
  let* bindings =
    all (List.zip_exn parts inferred) ~f:(fun ((p : S.pat), inferred) ->
        let* p, ty =
          match p.pat_desc with
          | Pcast (p, ty) ->
              let* ty = Source.ocaml_type env.ctx.env ~at:p.pat_loc ty in
              Ok (p, Some ty)
          | _ -> Ok (p, inferred)
        in
        match (p.pat_desc, ty) with
        | (Pid _ | Pwild), None ->
            error p.pat_loc "Add a type annotation to this proof binding"
        | Pid id, Some ty -> Ok (Some id, ty)
        | Pwild, Some ty -> Ok (None, ty)
        | _ ->
            error p.pat_loc "A proof let binding needs a variable or tuple of variables")
  in
  let ids =
    List.filter_map bindings ~f:(fun (id, _) -> Option.map id ~f:(fun id -> id.S.pid_str))
  in
  match List.find_a_dup ids ~compare:String.compare with
  | Some x -> error pattern.pat_loc (Printf.sprintf "Duplicate proof variable %s" x)
  | None -> Ok bindings

let proof_typed_env env bindings =
  List.fold bindings ~init:env ~f:(fun env (id, ty) ->
      match id with
      | None -> env
      | Some id ->
          {
            (bind env id.S.pid_str (Raven id.pid_str)) with
            var_types = (id.pid_str, ty) :: env.var_types;
          })

let proof_state ctx ~at =
  Option.value ctx.proof_state ~default:(unit_value ~loc:(loc at), Predef.type_unit)

let rec proof_pattern env (pattern : S.pat) ty value =
  match pattern.pat_desc with
  | Pwild -> Ok env
  | Pid id ->
      Ok
        {
          (bind env id.pid_str (Value value)) with
          var_types = (id.pid_str, ty) :: env.var_types;
        }
  | Pcast (pattern, annotation) ->
      let* expected = Source.ocaml_type env.ctx.env ~at:pattern.pat_loc annotation in
      if Ctype.is_equal env.ctx.env false [ expected ] [ ty ] then
        proof_pattern env pattern ty value
      else error pattern.pat_loc "The proof pattern has a different type from its input"
  | Ptuple [] when Ctype.is_equal env.ctx.env false [ ty ] [ Predef.type_unit ] -> Ok env
  | Ptuple patterns ->
      begin match Datatypes.desc env.data ty with
      | Ttuple types when List.length patterns = List.length types ->
          List.foldi patterns ~init:(Ok env) ~f:(fun i env pattern ->
              let* env = env in
              let _, ty = List.nth_exn types i in
              proof_pattern env pattern ty
                (R.Expr.tuple_get ~loc:(loc pattern.pat_loc) value i))
      | _ -> error pattern.pat_loc "The proof pattern does not match its input type"
      end
  | Pconstr _ | Pconst _ ->
      error pattern.pat_loc "A proof parameter needs an irrefutable pattern"

let bind_proof_pattern env pattern ty value =
  match List.find_a_dup (pat_names pattern) ~compare:String.compare with
  | Some x -> error pattern.S.pat_loc (Printf.sprintf "Duplicate proof variable %s" x)
  | None -> proof_pattern env pattern ty value

let packed_type = function
  | [] -> Predef.type_unit
  | [ ty ] -> ty
  | types -> Btype.newgenty (Ttuple (List.map types ~f:(fun ty -> (None, ty))))

let packed_value ~loc:l = function
  | [] -> unit_value ~loc:l
  | [ value ] -> value
  | values -> R.Expr.tuple ~loc:l values

let unpacked_value ~loc:l types value =
  match types with
  | [] -> []
  | [ _ ] -> [ value ]
  | types -> List.mapi types ~f:(fun i _ -> R.Expr.tuple_get ~loc:l value i)

(** Existentials are named by their declaration in the predicate, including those nested
    inside a match or another logical connective. *)
let rec predicate_existentials (t : S.term) =
  match t.term_desc with
  | Ttrue | Tfalse | Tconst _ | Tvar _ -> []
  | Tquant (Texists, bindings, body) -> bindings @ predicate_existentials body
  | Tquant (Tforall, _, body)
  | Tcomprehension (_, body)
  | Tattr (_, body)
  | Tcast (body, _)
  | Told body
  | Tfield (body, _) ->
      predicate_existentials body
  | Tapply (a, b) | Tinfix (a, _, b) | Tlet (_, a, b) ->
      predicate_existentials a @ predicate_existentials b
  | Tif (c, a, b) ->
      predicate_existentials c @ predicate_existentials a @ predicate_existentials b
  | Tmatch (scrutinee, cases) ->
      predicate_existentials scrutinee
      @ List.concat_map cases ~f:(fun (_, body) -> predicate_existentials body)
  | Ttuple ts -> List.concat_map ts ~f:predicate_existentials

let unfold_result_types env (t : S.term) witnesses =
  let head, _ = spine t [] in
  match head.term_desc with
  | Tvar q when List.Assoc.mem env.ctx.preds (logical_key env q) ~equal:String.equal ->
      let key = logical_key env q in
      let display = qualid_key q in
      let* () =
        if List.mem env.ctx.proof_support.opaque_predicates key ~equal:String.equal then
          error head.term_loc
            "The definition of this predicate is hidden by its module signature"
        else Ok ()
      in
      begin match List.Assoc.find env.ctx.predicate_bodies key ~equal:String.equal with
      | None -> Ok None
      | Some body ->
          let bindings = predicate_existentials body.definition in
          let* types =
            all witnesses ~f:(fun (witness : S.id) ->
                match
                  List.filter bindings ~f:(fun (id, _) ->
                      String.equal id.S.pid_str witness.pid_str)
                with
                | [] ->
                    error witness.pid_loc
                      (Printf.sprintf "Predicate %s has no existential named %s" display
                         witness.pid_str)
                | [ (_, Some ty) ] ->
                    let* ty = Source.ocaml_type body.environment ~at:witness.pid_loc ty in
                    Ok (Some (body.project_type ty))
                | [ (_, None) ] ->
                    error witness.pid_loc "An existential variable needs a type"
                | _ ->
                    error witness.pid_loc
                      (Printf.sprintf "Existential name %s is ambiguous in predicate %s"
                         witness.pid_str display))
          in
          Ok (Some types)
      end
  | _ -> error t.term_loc "Expected a predicate applied to its arguments"

let rec proof_result_types env (body : S.proof_expr) =
  match body.proof_desc with
  | Proof_value t
    when is_ghost_fpu t || Option.equal String.equal (ghost_operation t) (Some "write") ->
      Ok (Some [])
  | Proof_value t ->
      let* ts = proof_value_types env t in
      Ok (Some ts)
  | Proof_assert { term_desc = Tfalse; _ } -> Ok None
  | Proof_assert _ | Proof_fold _ -> Ok (Some [])
  | Proof_unfold (_, []) -> Ok (Some [])
  | Proof_unfold (predicate, witnesses) -> unfold_result_types env predicate witnesses
  | Proof_seq (_, body) -> proof_result_types env body
  | Proof_if (_, yes, no) ->
      let* types = proof_result_types env yes in
      begin match types with Some _ -> Ok types | None -> proof_result_types env no
      end
  | Proof_match (_, []) -> error body.proof_loc "A match needs at least one case"
  | Proof_match (scrutinee, cases) ->
      let* scrutinee_type = proof_value_type env scrutinee in
      let rec infer = function
        | [] -> Ok None
        | (p, body) :: rest ->
            let types =
              Option.value_map scrutinee_type ~default:[] ~f:(pattern_types env p)
            in
            let branch_env =
              List.fold types
                ~init:{ env with var_types = types @ env.var_types }
                ~f:(fun env (x, _) -> bind env x (Raven x))
            in
            let* types = proof_result_types branch_env body in
            begin match types with Some _ -> Ok types | None -> infer rest
            end
      in
      infer cases
  | Proof_let (pattern, rhs, body) ->
      let* inferred = proof_result_types env rhs in
      let* bindings = proof_binding_types env pattern inferred in
      proof_result_types (proof_typed_env env bindings) body

(** Lexical expressions assign only to fresh internal result variables. *)
let rec proof_expression env targets (body : S.proof_expr) =
  let l = loc body.proof_loc in
  let target_expr target = R.Expr.var ~loc:l (name ~loc:l target.target_name) in
  let unit_statement statement =
    match targets with
    | [] -> Ok [ statement ]
    | [ target ] when is_unit target.target_type ->
        Ok
          [
            statement;
            R.Stmt.assign ~loc:l
              [ target_expr target ]
              (R.Stmt.expr_rhs (R.Expr.tuple ~loc:l []));
          ]
    | _ -> error body.proof_loc "This proof expression returns unit"
  in
  match body.proof_desc with
  | Proof_value t when is_ghost_fpu t ->
      let* statement = ghost_fpu env t in
      unit_statement statement
  | Proof_value t when Option.equal String.equal (ghost_operation t) (Some "write") ->
      begin match snd (spine t []) with
      | [ location; value ] ->
          let* field, location = ghost_value_location env location in
          let* () =
            Source.check_logical_expression env.ctx.env
              ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types
              ~expected:field.field_value value
          in
          let* value = expected_formula env (Some field.field_value) value in
          unit_statement (R.Stmt.assign ~loc:l [ location ] (R.Stmt.expr_rhs value))
      | _ -> error t.term_loc "Ghost.write expects a location and a value"
      end
  | Proof_value t when Option.equal String.equal (ghost_operation t) (Some "read") ->
      begin match (snd (spine t []), targets) with
      | [ location ], [ target ] ->
          let* field, location = ghost_value_location env location in
          let* () =
            if
              Ctype.is_equal env.ctx.env false [ field.field_value ]
                [ target.target_type ]
            then Ok ()
            else error t.term_loc "The ghost read has a different result type"
          in
          Ok [ R.Stmt.assign ~loc:l [ target_expr target ] (R.Stmt.expr_rhs location) ]
      | _ -> error t.term_loc "Bind the result of Ghost.read location"
      end
  | Proof_value t when Option.equal String.equal (ghost_operation t) (Some "alloc") ->
      begin match (snd (spine t []), targets) with
      | [ initializers ], [ target ] ->
          let* owner = Source.ghost_type env.ctx.env ~at:t.term_loc in
          let* () =
            if Ctype.is_equal env.ctx.env false [ owner ] [ target.target_type ] then
              Ok ()
            else error t.term_loc "Ghost.alloc returns Ghost.t"
          in
          let* fields = ghost_initializers env ~owner initializers in
          Ok [ R.Stmt.assign ~loc:l [ target_expr target ] (R.Stmt.new_rhs fields) ]
      | _ -> error t.term_loc "Bind the result of Ghost.alloc initializers"
      end
  | Proof_value t ->
      begin match proof_signature env t with
      | Some signature ->
          let* () =
            if
              Ctype.is_equal env.ctx.env false
                [ packed_type signature.lemma_outputs ]
                [ packed_type (List.map targets ~f:(fun t -> t.target_type)) ]
            then Ok ()
            else
              error t.term_loc
                "The proof expression has a different result type from its binding"
          in
          let* call, outputs = proof_call env t in
          if List.length outputs = List.length targets then
            if List.is_empty targets then Ok [ R.Stmt.call ~loc:l call ]
            else
              Ok
                [
                  R.Stmt.assign ~loc:l
                    (List.map targets ~f:target_expr)
                    (R.Stmt.expr_rhs call);
                ]
          else
            begin match targets with
            | [ target ] ->
                let* temporaries =
                  all outputs ~f:(fun ty ->
                      let raven = Names.fresh env.ctx.names "result" in
                      let* raven_type = typ env.ctx ~at:t.term_loc ty in
                      let target = { target_name = raven; target_type = ty } in
                      Ok
                        ( target,
                          R.Stmt.local ~loc:l ~ghost:true ~typ:raven_type
                            (ident ~loc:l raven) ))
                in
                let values =
                  List.map temporaries ~f:(fun (target, _) -> target_expr target)
                in
                let call =
                  if List.is_empty values then R.Stmt.call ~loc:l call
                  else R.Stmt.assign ~loc:l values (R.Stmt.expr_rhs call)
                in
                let result = R.Expr.tuple ~loc:l values in
                Ok
                  (List.concat_map temporaries ~f:snd
                  @ [
                      call;
                      R.Stmt.assign ~loc:l [ target_expr target ] (R.Stmt.expr_rhs result);
                    ])
            | _ ->
                begin match outputs with
                | [ ty ] when not (List.is_empty targets) ->
                    let raven = Names.fresh env.ctx.names "result" in
                    let* raven_type = typ env.ctx ~at:t.term_loc ty in
                    let result = R.Expr.var ~loc:l (name ~loc:l raven) in
                    let declaration =
                      R.Stmt.local ~loc:l ~ghost:true ~typ:raven_type (ident ~loc:l raven)
                    in
                    let assignments =
                      List.mapi targets ~f:(fun i target ->
                          R.Stmt.assign ~loc:l
                            [ target_expr target ]
                            (R.Stmt.expr_rhs (R.Expr.tuple_get ~loc:l result i)))
                    in
                    Ok
                      (declaration
                      @ [ R.Stmt.assign ~loc:l [ result ] (R.Stmt.expr_rhs call) ]
                      @ assignments)
                | _ -> error t.term_loc "Bind all the results of this lemma"
                end
            end
      | None ->
          let values =
            match (targets, t.term_desc) with
            | [ _ ], _ -> [ t ]
            | _, Ttuple ts -> ts
            | _ -> [ t ]
          in
          if List.is_empty targets && not (List.is_empty values) then
            let* _, _ = lemma_call env t in
            error t.term_loc "This expression does not return unit"
          else if List.length values <> List.length targets then
            begin match values with
            | [ value ] when not (List.is_empty targets) ->
                let* () =
                  Source.check_logical_expression env.ctx.env
                    ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types
                    ~expected:(packed_type (List.map targets ~f:(fun t -> t.target_type)))
                    value
                in
                let* value = formula env value in
                Ok
                  (List.mapi targets ~f:(fun i target ->
                       R.Stmt.assign ~loc:l
                         [ target_expr target ]
                         (R.Stmt.expr_rhs (R.Expr.tuple_get ~loc:l value i))))
            | _ ->
                error t.term_loc
                  "This expression does not match the expected proof results"
            end
          else
            all (List.zip_exn targets values) ~f:(fun (target, value) ->
                let* () =
                  Source.check_logical_expression env.ctx.env
                    ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types
                    ~expected:target.target_type value
                in
                let* value = expected_formula env (Some target.target_type) value in
                Ok (R.Stmt.assign ~loc:l [ target_expr target ] (R.Stmt.expr_rhs value)))
      end
  | Proof_assert t ->
      let* value = formula env t in
      let statement = R.Stmt.assert_ ~loc:l (R.Spec.make value) in
      begin match t.term_desc with
      | Tfalse -> Ok [ statement ]
      | _ -> unit_statement statement
      end
  | Proof_fold (t, witnesses) ->
      let* statement = predicate_use env ~unfold:false t witnesses R.Stmt.fold in
      unit_statement statement
  | Proof_unfold (t, []) ->
      let* statement = predicate_use env ~unfold:true t [] R.Stmt.unfold in
      unit_statement statement
  | Proof_unfold (t, witnesses) ->
      let* _ = unfold_result_types env t witnesses in
      if List.length targets <> List.length witnesses then
        error body.proof_loc "Bind every named existential returned by unfold"
      else
        let env, witnesses =
          List.fold (List.zip_exn targets witnesses) ~init:(env, [])
            ~f:(fun (env, ws) (target, existential) ->
              let id = S.mk_id ~loc:body.proof_loc target.target_name in
              let value = S.mk_term (Tvar (Qid existential)) existential.pid_loc in
              (bind env target.target_name (Raven target.target_name), (id, value) :: ws))
        in
        let* statement =
          predicate_use env ~unfold:true t (List.rev witnesses) R.Stmt.unfold
        in
        Ok [ statement ]
  | Proof_seq (first, rest) ->
      let* first = proof_expression env [] first in
      let* rest = proof_expression env targets rest in
      Ok (first @ rest)
  | Proof_if (condition, yes, no) ->
      let* condition = expected_formula env (Some Predef.type_bool) condition in
      let* yes = proof_expression env targets yes in
      let* no = proof_expression env targets no in
      Ok [ R.Stmt.if_ ~loc:l condition yes no ]
  | Proof_let (pattern, rhs, rest) ->
      proof_binding env pattern rhs (fun env -> proof_expression env targets rest)
  | Proof_match (scrutinee, cases) ->
      let* value = formula env scrutinee in
      let* scrutinee_type = proof_value_type env scrutinee in
      let rec chain = function
        | [] ->
            Ok
              [
                check env.ctx ~at:body.proof_loc "This match may not be exhaustive"
                  (R.Expr.bool ~loc:l false);
              ]
        | (pattern, body) :: rest ->
            let* () =
              match List.find_a_dup (pat_names pattern) ~compare:String.compare with
              | None -> Ok ()
              | Some x ->
                  error pattern.pat_loc (Printf.sprintf "Duplicate proof variable %s" x)
            in
            let* condition, bindings = spec_pattern env pattern value in
            let types =
              Option.value_map scrutinee_type ~default:[] ~f:(pattern_types env pattern)
            in
            let branch_env =
              List.fold bindings
                ~init:{ env with var_types = types @ env.var_types }
                ~f:(fun env (x, value) -> bind env x (Value value))
            in
            let* branch = proof_expression branch_env targets body in
            begin match condition with
            | None -> Ok branch
            | Some condition ->
                let* rest = chain rest in
                Ok [ R.Stmt.if_ ~loc:l condition branch rest ]
            end
      in
      chain cases

and proof_binding ?(ghost_rhs = false) env pattern rhs continuation =
  let l = loc rhs.S.proof_loc in
  let* inferred = proof_result_types env rhs in
  let* bindings = proof_binding_types env pattern inferred in
  let* declarations =
    all bindings ~f:(fun (id, ty) ->
        let id = Option.value id ~default:(S.mk_id ~loc:pattern.pat_loc "discard") in
        let raven = Names.fresh env.ctx.names id.pid_str in
        let* raven_type = typ env.ctx ~at:id.pid_loc ty in
        Ok
          ( id,
            { target_name = raven; target_type = ty },
            R.Stmt.local ~loc:(loc id.pid_loc) ~ghost:true ~typ:raven_type
              (ident ~loc:l raven) ))
  in
  let* rhs_statements =
    proof_expression env (List.map declarations ~f:(fun (_, target, _) -> target)) rhs
  in
  let env =
    List.fold (List.zip_exn bindings declarations) ~init:env
      ~f:(fun env ((id, ty), (_, target, _)) ->
        match id with
        | None -> env
        | Some id ->
            {
              (bind env id.pid_str (Raven target.target_name)) with
              var_types = (id.pid_str, ty) :: env.var_types;
            })
  in
  let* rest = continuation env in
  let rhs =
    if ghost_rhs then [ R.Stmt.ghost_block ~loc:(loc rhs.proof_loc) rhs_statements ]
    else rhs_statements
  in
  Ok (List.concat_map declarations ~f:(fun (_, _, stmts) -> stmts) @ rhs @ rest)

(** Ghost annotations share the checked lemma expression language. *)
let ghost ctx ~(after : Lexing.position) ~(before : Lexing.position) =
  let between (a : Annotation.t) =
    a.loc.loc_start.pos_cnum >= after.pos_cnum
    && a.loc.loc_end.pos_cnum <= before.pos_cnum
    && List.mem
         [ Annotation.Ghost; Annotation.Proof ]
         (Annotation.kind a) ~equal:Poly.equal
  in
  let* blocks =
    all (List.filter ctx.annotations ~f:between) ~f:(fun annotation ->
        match Annotation.kind annotation with
        | Annotation.Proof ->
            let* body = Annotation.proof annotation in
            let* statements = proof_expression (scope_env ctx) [] body in
            Ok [ R.Stmt.ghost_block ~loc:(loc annotation.loc) statements ]
        | _ ->
            let* statements = Annotation.ghost_stmts annotation in
            all statements ~f:(proof_statement (scope_env ctx)))
  in
  Ok (List.concat blocks)

(** Free names in proof expressions, respecting lexical bindings. *)
let rec proof_names (body : S.proof_expr) =
  match body.proof_desc with
  | Proof_value t | Proof_assert t | Proof_unfold (t, _) -> term_names t
  | Proof_fold (t, witnesses) ->
      term_names t @ List.concat_map witnesses ~f:(fun (_, t) -> term_names t)
  | Proof_seq (a, b) -> proof_names a @ proof_names b
  | Proof_let (pattern, rhs, rest) ->
      proof_names rhs
      @ List.filter (proof_names rest) ~f:(fun name ->
          not (List.mem (pat_names pattern) name ~equal:String.equal))
  | Proof_if (t, a, b) -> term_names t @ proof_names a @ proof_names b
  | Proof_match (t, cases) ->
      term_names t
      @ List.concat_map cases ~f:(fun (p, body) ->
          List.filter (proof_names body) ~f:(fun name ->
              not (List.mem (pat_names p) name ~equal:String.equal)))

let stateful_access access_proofs (e : Typedtree.expression) =
  let key = (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum) in
  match List.Assoc.find access_proofs key ~equal:Poly.equal with
  | None -> Ok false
  | Some annotation ->
      Result.map (Annotation.scope annotation) ~f:(fun scope ->
          Option.is_some scope.scope_state)

let atomic_read_argument (e : Typedtree.expression) =
  match e.exp_desc with
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, [ (_, Arg argument) ])
    when Option.equal String.equal (atomic_name path) (Some "get") ->
      Some argument
  | _ -> None

(** State stays local to a directly nested pair of explicitly stateful reads. *)
let nested_stateful_read access_proofs e =
  match atomic_read_argument e with
  | Some argument when Option.is_some (atomic_read_argument argument) ->
      let* outer = stateful_access access_proofs e in
      let* inner = stateful_access access_proofs argument in
      Ok (Option.some_if (outer && inner) argument)
  | _ -> Ok None

(** A checked wrapper invokes the original operation once. *)
let access_proof ctx annotation ~result_type ?(input_types = []) ?(output_types = []) run
    =
  let* scope = Annotation.scope annotation in
  let operation = scope.scope_operation and body = scope.scope_body in
  let uses_operation body =
    List.mem (proof_names body) operation.pid_str ~equal:String.equal
  in
  let reject_operation visible body =
    if visible && uses_operation body then
      error body.S.proof_loc "Bind the attached operation once in an unconditional let"
    else Ok ()
  in
  let ghost_statements env body =
    let* statements = proof_expression env [] body in
    Ok [ R.Stmt.ghost_block ~loc:(loc body.S.proof_loc) statements ]
  in
  let finish_state env (state : S.term) =
    let* ty = proof_value_type env state in
    match ty with
    | None -> error state.term_loc "Add a type annotation to the output proof state"
    | Some ty ->
        let* () =
          Source.check_logical_expression env.ctx.env
            ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types ~expected:ty
            state
        in
        let* value = expected_formula env (Some ty) state in
        let raven = Names.fresh ctx.names "proof_state" in
        let* raven_type = typ ctx ~at:state.term_loc ty in
        let l = loc state.term_loc in
        let result = R.Expr.var ~loc:l (name ~loc:l raven) in
        ctx.proof_state <- Some (result, ty);
        Ok
          (R.Stmt.local ~loc:l ~ghost:true ~typ:raven_type (ident ~loc:l raven)
          @ [
              R.Stmt.ghost_block ~loc:l
                [ R.Stmt.assign ~loc:l [ result ] (R.Stmt.expr_rhs value) ];
            ])
  in
  let rec after env ~operation_visible ~result_name ~result_visible body =
    let* () = reject_operation operation_visible body in
    let unchanged (t : S.term) =
      match t.term_desc with
      | Tvar (Qid id) -> result_visible && String.equal id.pid_str result_name
      | _ -> false
    in
    match body.S.proof_desc with
    | Proof_value t when Option.is_none scope.scope_state && unchanged t -> Ok []
    | Proof_value { term_desc = Ttuple [ runtime; state ]; _ }
      when Option.is_some scope.scope_state && unchanged runtime ->
        finish_state env state
    | Proof_seq (first, rest) ->
        let* first = ghost_statements env first in
        let* rest = after env ~operation_visible ~result_name ~result_visible rest in
        Ok (first @ rest)
    | Proof_let (pattern, rhs, rest) ->
        proof_binding ~ghost_rhs:true env pattern rhs (fun env ->
            after env
              ~operation_visible:
                (operation_visible
                && not
                     (List.mem (pat_names pattern) operation.pid_str ~equal:String.equal)
                )
              ~result_name
              ~result_visible:
                (result_visible
                && not (List.mem (pat_names pattern) result_name ~equal:String.equal))
              rest)
    | _ ->
        error body.proof_loc
          (if Option.is_some scope.scope_state then
             "A stateful scope must return (unchanged operation result, output state)"
           else
             "An access proof must return the unchanged result of the attached operation")
  in
  let operation_argument visible body =
    match body.S.proof_desc with
    | Proof_value t when visible ->
        begin match spine t [] with
        | { term_desc = Tvar (Qid id); _ }, [ argument ]
          when String.equal id.pid_str operation.pid_str ->
            Some argument
        | _ -> None
        end
    | _ -> None
  in
  let rec runtime_binding (p : S.pat) =
    match p.pat_desc with
    | Pid id -> Some id
    | Pcast (p, _) -> runtime_binding p
    | _ -> None
  in
  let rec operation_result (p : S.pat) =
    if List.is_empty output_types then runtime_binding p
    else
      match p.pat_desc with
      | Ptuple [ runtime; _ ] -> runtime_binding runtime
      | Pcast (p, _) -> operation_result p
      | _ -> None
  in
  let rec before env visible body =
    match body.S.proof_desc with
    | Proof_let (pattern, rhs, rest) when Option.is_some (operation_argument visible rhs)
      ->
        let argument = Option.value_exn (operation_argument visible rhs) in
        let* () =
          Source.check_logical_expression env.ctx.env
            ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types
            ~expected:(packed_type input_types) argument
        in
        let* argument = expected_formula env (Some (packed_type input_types)) argument in
        let arguments = unpacked_value ~loc:(loc rhs.proof_loc) input_types argument in
        let* statements, result, outputs = run arguments in
        let result_value, result_ty =
          if List.is_empty output_types then (result, result_type)
          else
            ( R.Expr.tuple ~loc:(loc rhs.proof_loc)
                [ result; packed_value ~loc:(loc rhs.proof_loc) outputs ],
              packed_type [ result_type; packed_type output_types ] )
        in
        let* env = bind_proof_pattern env pattern result_ty result_value in
        begin match operation_result pattern with
        | None ->
            error pattern.pat_loc
              "Bind the operation's runtime result to a variable of its original type"
        | Some id ->
            let* rest =
              after env
                ~operation_visible:
                  (not
                     (List.mem (pat_names pattern) operation.pid_str ~equal:String.equal))
                ~result_name:id.pid_str ~result_visible:true rest
            in
            Ok (statements @ rest)
        end
    | Proof_let (pattern, rhs, rest) ->
        let* () = reject_operation visible rhs in
        proof_binding ~ghost_rhs:true env pattern rhs (fun env ->
            before env
              (visible
              && not (List.mem (pat_names pattern) operation.pid_str ~equal:String.equal)
              )
              rest)
    | Proof_seq (first, rest) ->
        let* () = reject_operation visible first in
        let* first = ghost_statements env first in
        let* rest = before env visible rest in
        Ok (first @ rest)
    | _ ->
        error body.proof_loc
          "An access proof needs one unconditional let binding of the attached operation"
  in
  let* env =
    match scope.scope_state with
    | None -> Ok (scope_env ctx)
    | Some pattern ->
        let value, ty = proof_state ctx ~at:pattern.pat_loc in
        bind_proof_pattern (scope_env ctx) pattern ty value
  in
  let visible =
    not
      (Option.exists scope.scope_state ~f:(fun p ->
           List.mem (pat_names p) operation.pid_str ~equal:String.equal))
  in
  before env visible body

let return_proof ctx annotation ~result_type ~result =
  let* adapter = Annotation.returns annotation in
  if List.is_empty ctx.ghost_returns then
    error annotation.Annotation.loc "Ghost.returns requires declared ghost results"
  else
    let* env =
      bind_proof_pattern (scope_env ctx) adapter.returns_result result_type result
    in
    let value, ty = proof_state ctx ~at:adapter.returns_state.pat_loc in
    let* env = bind_proof_pattern env adapter.returns_state ty value in
    let targets =
      List.map ctx.ghost_returns ~f:(fun (_, raven, ty) ->
          { target_name = raven; target_type = ty })
    in
    let* statements = proof_expression env targets adapter.returns_body in
    Ok [ R.Stmt.ghost_block ~loc:(loc annotation.loc) statements ]

(** The specification of the loop whose body is [body], in an annotation between [after]
    and the body, as [while c do (*@ invariant P *) ... done]. *)
let loop_spec ctx ~(after : Location.t) (body : Typedtree.expression) =
  let between (a : Annotation.t) =
    a.loc.loc_start.pos_cnum >= after.loc_end.pos_cnum
    && a.loc.loc_end.pos_cnum <= body.exp_loc.loc_start.pos_cnum
  in
  match
    List.filter ctx.annotations ~f:(fun a ->
        between a && Poly.equal (Annotation.kind a) Annotation.Loop)
  with
  | [] -> Ok { S.invariants = []; state_invariants = []; loop_variant = [] }
  | [ a ] -> Annotation.loop_spec a
  | _ :: a :: _ -> error a.loc "A loop has at most one annotation"

(** The invariants of a loop at [at]: those of [spec], with the variables in scope there,
    the facts that hold throughout the function, and the ranges of the integer variables
    in scope but a [for] loop's [counter], which goes one beyond. Names free in [spec]'s
    invariants are existentially quantified, as [k] in [invariant own i.contents k];
    [relation], given the values these own, as [k] for [i.contents], may add a conjunct,
    as the value of the loop's condition. *)
let rec loop_invariants ?(counter = "") ctx ~at (spec : S.loop_spec)
    ~(relation : ((string * string) * R.Expr.t) list -> (R.Expr.t option, error) Result.t)
    =
  let l = loc at in
  let* () =
    match spec.loop_variant with
    | [] -> Ok ()
    | v :: _ -> unsupported v.term_loc "A variant"
  in
  let scope = scope ctx in
  let env = scope_env ctx in
  let* env, state_invariants =
    List.fold spec.state_invariants
      ~init:(Ok (env, []))
      ~f:(fun acc (pattern, body) ->
        let* env, terms = acc in
        let value, ty = proof_state ctx ~at:pattern.S.pat_loc in
        let* _ = bind_proof_pattern env pattern ty value in
        let source = Names.fresh ctx.names "caravan$loop_state" in
        let id = S.mk_id ~loc:pattern.pat_loc source in
        let variable = S.mk_term (Tvar (Qid id)) pattern.pat_loc in
        let term = S.mk_term (Tlet (pattern, variable, body)) body.term_loc in
        let env =
          {
            (bind env source (Value value)) with
            var_types = (source, ty) :: env.var_types;
          }
        in
        Ok (env, terms @ [ term ]))
  in
  let terms = spec.invariants @ state_invariants in
  let* free = free_typed env terms ~at in
  let env =
    List.fold free ~init:env ~f:(fun env (x, raven, t, _, _) ->
        { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
  in
  let* invariants = all terms ~f:(formula env) in
  (* The values that the invariants own, by the Raven names of their references and
     fields. *)
  let* reads =
    all (List.concat_map terms ~f:owned_names) ~f:(fun (x, label, v) ->
        match
          ( List.Assoc.find env.vars x ~equal:String.equal,
            List.Assoc.find env.var_types x ~equal:String.equal,
            List.Assoc.find env.vars v ~equal:String.equal )
        with
        | Some (Raven r), Some t, Some (Raven v) ->
            let* field = field_of_type ctx ~at t label in
            Ok
              (Option.map field ~f:(fun field ->
                   ((r, field), R.Expr.var ~loc:l (name ~loc:l v))))
        | _ -> Ok None)
  in
  let* related = relation (List.filter_opt reads) in
  let invariants = invariants @ Option.to_list related in
  let user =
    match (free, invariants) with
    | _, [] -> []
    | [], _ -> List.map invariants ~f:R.Spec.make
    | _, i :: is ->
        let vars =
          List.map free ~f:(fun (_, raven, _, typ, l) ->
              R.Var.make ~loc:l (ident ~loc:l raven) typ)
        in
        let conj = List.fold is ~init:i ~f:(fun a b -> R.Expr.binary ~loc:l And a b) in
        [ R.Spec.make (R.Expr.exists ~loc:l vars conj) ]
  in
  let ranges =
    List.filter_map scope ~f:(fun (_, (raven, t)) ->
        if String.equal raven counter then None
        else Option.bind t ~f:(fun t -> range_spec ~loc:l t raven))
  in
  Ok (ranges @ ctx.facts @ user)

(** The names that [t] owns the values of fields of variables as, as [k] for [i.contents]
    in [own i.contents k]: the variable, the field and the name. *)
and owned_names (t : S.term) =
  match (owned_location t, t.term_desc) with
  | Some owned, _ -> [ owned ]
  | None, (Tapply (a, b) | Tinfix (a, _, b)) -> owned_names a @ owned_names b
  | None, Tif (a, b, c) -> owned_names a @ owned_names b @ owned_names c
  | None, (Tattr (_, t) | Tcast (t, _)) -> owned_names t
  | None, _ -> []

(** Where the ghost fields of a structure of type [t] go: on its reference, or, for an
    immutable record, on its first atomic. The field whose allocation allocates them, and
    the reference, given the structure. *)
let anchor (types : Datatypes.t list) (t : Types.type_expr) :
    (string * (loc:R.Loc.t -> R.Expr.t -> R.Expr.t)) option =
  let itself ~loc:_ e = e in
  match Datatypes.desc types t with
  | Tconstr (p, [ elt ], _) when Datatypes.is_atomic p ->
      Some ("atomic_" ^ Datatypes.tag types elt, itself)
  | Tconstr (p, [ elt ], _) when Datatypes.is_ref p ->
      Some ("ref_" ^ Datatypes.tag types elt ^ "_contents", itself)
  | Tconstr (p, [], _) ->
      begin match Datatypes.find types p with
      | Some { heap = Some (f :: _); _ } -> Some (f.raven_field, itself)
      | Some { heap = None; ctors = [ { ocaml = ""; fields; args; _ } ]; _ } ->
          List.find_map (List.zip_exn fields args) ~f:(fun (label, a) ->
              match Datatypes.desc types a with
              | Tconstr (q, [ elt ], _) when Datatypes.is_atomic q ->
                  Some
                    ( "atomic_" ^ Datatypes.tag types elt,
                      fun ~loc e -> R.Expr.field ~loc e (qualified_name ~loc label) )
              | _ -> None)
      | _ -> None
      end
  | _ -> None

(** The reference holding the ghost fields of the structure [e], the first argument of the
    predicate [pred]. *)
let anchored ctx ~loc ~pred (e : R.Expr.t) =
  match List.Assoc.find ctx.preds pred ~equal:String.equal with
  | Some (_, t :: _) ->
      begin match anchor ctx.types t with Some (_, at) -> at ~loc e | None -> e
      end
  | _ -> e

(** The environment of an action's terms: the state [values] of [st], its parameters with
    their [bindings] and the invariant's parameters, with the values [args]. *)
let action_env ctx st inv_params args values bindings =
  let ctx =
    {
      ctx with
      env = st.environment;
      preds = st.context.declaration_predicates;
      spec_funcs = st.context.declaration_functions;
      proof_support = st.context.declaration_support;
    }
  in
  let env = { (scope_env ctx) with vars = []; var_types = [] } in
  let env =
    bind env st.state
      (State (List.map2_exn st.fields values ~f:(fun (f, _, _, t, _) v -> (f, (v, t)))))
  in
  let env =
    List.fold
      (List.zip_exn inv_params (List.take args (List.length inv_params)))
      ~init:env
      ~f:(fun env ((x, t), e) ->
        { (bind env x (Value e)) with var_types = (x, t) :: env.var_types })
  in
  List.fold bindings ~init:env ~f:(fun env (x, e) -> bind env x (Value e))

(** The state after [p] of [st] from [opened], whose invariant has the parameters
    [inv_params] and the arguments [args]: each field's value, whether it changes, the
    index map of each field owned by index that it changes, as a list that it appends an
    entry to, and the entries appended, with their fields and positions. *)
let next_state ctx st ~inv_params args (opened : opened) (p : performing) =
  let env = action_env ctx st inv_params args opened.values p.bindings in
  let next =
    List.map2_exn st.fields opened.values ~f:(fun (f, _, _, t, _) v ->
        match List.Assoc.find p.performed.update f ~equal:String.equal with
        | Some term ->
            begin match expected_formula env (Some t) term with
            | Ok e -> (e, true)
            | Error _ -> (v, false)
            end
        | None -> (v, false))
  in
  (* An entry appended to a field owned by index, at the field's length. *)
  let appended field =
    match List.Assoc.find p.performed.update field ~equal:String.equal with
    | None -> None
    | Some term ->
        begin match spine (S.chain term) [] with
        | ( { term_desc = Tvar (Qid { pid_str = "++"; _ }); _ },
            [
              { term_desc = Tfield (_, Qid { pid_str = f; _ }); _ };
              ({ term_desc = Tapply _; _ } as added);
            ] )
          when String.equal f field ->
            begin match spine added [] with
            | ( { term_desc = Tvar (Qid { pid_str = "::"; _ }); _ },
                [ e; { term_desc = Tvar (Qid { pid_str = "[]"; _ }); _ } ] ) ->
                Result.ok (formula env e)
            | _ -> None
            end
        | _ -> None
        end
  in
  let appended =
    List.filter_map st.chains ~f:(fun (field, index) ->
        let i, _ =
          List.findi_exn st.fields ~f:(fun _ (f, _, _, _, _) -> String.equal f field)
        in
        Option.map (appended field) ~f:(fun e ->
            let l = R.Loc.none in
            ( field,
              index,
              e,
              R.Expr.call ~loc:l
                (R.Name.make ~loc:l ~path:[ "Seq" ] "length")
                [ List.nth_exn opened.values i ] )))
  in
  let indices =
    List.map appended ~f:(fun (field, index, e, position) ->
        ( index,
          R.Expr.update ~loc:R.Loc.none
            (List.Assoc.find_exn opened.indices field ~equal:String.equal)
            e position ))
  in
  ( next,
    indices,
    List.map appended ~f:(fun (field, _, e, position) -> (field, e, position)) )

(** The views of [st], whose invariant has the arguments [args], in the state [values]:
    each view, its inputs and its value. *)
let views_after ctx st args values =
  let env = action_env ctx st st.params args values [] in
  all st.views ~f:(fun ((v : S.predicate), value) ->
      let inputs = List.take args (List.length v.pred_params - 1) in
      let env =
        List.fold2_exn (List.drop_last_exn v.pred_params) inputs ~init:env
          ~f:(fun env (id, _) e -> bind env id.S.pid_str (Value e))
      in
      let* value = formula env value in
      Ok (v.pred_name.pid_str, inputs, value))

(** The statements opening the invariants the function holds before the step at [at], or
    with [fold] closing them after it, where a failure is reported. *)
let use_invariants ?performs ?(no_action = false) ctx ~(at : Location.t) ~fold =
  let after = { at with loc_start = at.loc_end } in
  let l = loc at and la = loc after in
  let var x = R.Expr.var ~loc:l (name ~loc:l x) in
  let structure inv =
    List.find ctx.shared.structures ~f:(fun st -> String.equal st.invariant inv)
  in
  let state_value st values =
    R.Expr.call ~loc:l
      (generated_module_member ~loc:l (module_name st "state") "state")
      (grown st values)
  in
  let lemma f args =
    R.Stmt.call ~loc:l (R.Expr.call ~loc:l (qualified_name ~loc:l f) args)
  in
  List.concat_map ctx.invariants ~f:(fun (inv, args) ->
      match (fold, structure inv) with
      | false, Some st ->
          (* The state, and the index maps, bound to variables. *)
          let local (raven, typ) = (raven, Names.fresh ctx.names raven, typ) in
          let locals =
            List.map st.fields ~f:(fun (_, raven, typ, _, _) -> local (raven, typ))
          in
          let index_locals =
            List.map st.chains ~f:(fun (field, raven) ->
                (field, local (raven, chain_index_type ctx.types st field)))
            @ List.map st.pendings ~f:(fun p ->
                let key =
                  Option.value
                    (Result.ok (Datatypes.typ ctx.types ~at p.key_type))
                    ~default:(R.Type.ref ~loc:l)
                in
                ( p.pending_field,
                  local (p.pending_on, R.Type.map ~loc:l (R.Type.ref ~loc:l) key) ))
          in
          ctx.opened <-
            ( inv,
              {
                values = List.map locals ~f:(fun (_, x, _) -> var x);
                indices = List.map index_locals ~f:(fun (f, (_, x, _)) -> (f, var x));
              } )
            :: List.Assoc.remove ctx.opened inv ~equal:String.equal;
          let all_locals = locals @ List.map index_locals ~f:snd in
          (* The entries of earlier snapshots are still at their positions. *)
          let current =
            state_of ~loc:l st (grown st (List.map locals ~f:(fun (_, x, _) -> var x)))
          in
          let kept =
            if has_history st then
              List.concat_map
                (List.filter ctx.positions ~f:(fun p -> String.equal p.pos_inv inv))
                ~f:(fun p ->
                  [
                    lemma (member_name st "observe")
                      [ List.hd_exn args; p.pos_snapshot; current ];
                    lemma
                      (member_name st ("kept_" ^ p.pos_field))
                      [ p.pos_snapshot; current; p.pos_k ];
                  ])
            else []
          in
          List.concat_map all_locals ~f:(fun (_, x, typ) ->
              R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x))
          @ [
              R.Stmt.unfold ~loc:l
                ~witnesses:
                  (List.map all_locals ~f:(fun (e, x, _) -> (ident ~loc:l x, var e)))
                (qualified_name ~loc:l inv) args;
            ]
          @ kept
      | false, None -> [ R.Stmt.unfold ~loc:l (qualified_name ~loc:l inv) args ]
      | true, _ -> (
          let definition =
            Option.to_list
              (Option.map (List.Assoc.find ctx.shared.persistent inv ~equal:String.equal)
                 ~f:(fun def -> (def, "The invariant")))
          in
          ctx.origins :=
            {
              at = after;
              code = Fold;
              message = Printf.sprintf "The invariant %s may not hold after this step" inv;
              related = definition;
            }
            :: !(ctx.origins);
          (* A step that performs none of the actions whose step it may be keeps the state
             as it is: its fold is at the step, with a message of its own. *)
          if no_action then
            ctx.origins :=
              {
                at;
                code = Fold;
                message =
                  Printf.sprintf
                    "This step may change the state of %s in a way that no action \
                     allows; if it performs one, say so, as (*@ performs a *)"
                    inv;
                related = definition;
              }
              :: !(ctx.origins);
          let fold ?(witnesses = []) () =
            let l = if no_action then l else la in
            [ R.Stmt.fold ~loc:l ~witnesses (qualified_name ~loc:l inv) args ]
          in
          let snapshot st (state : opened) =
            let snapshots =
              Option.value
                (List.Assoc.find ctx.snapshots inv ~equal:String.equal)
                ~default:[]
            in
            ctx.snapshots <-
              (inv, state :: snapshots)
              :: List.Assoc.remove ctx.snapshots inv ~equal:String.equal;
            lemma (member_name st "snapshot")
              [ List.hd_exn args; state_value st state.values ]
          in
          match (structure inv, List.Assoc.find ctx.opened inv ~equal:String.equal) with
          | Some st, Some opened ->
              let witnesses (state : opened) =
                List.map2_exn st.fields state.values ~f:(fun (_, raven, _, _, _) value ->
                    (ident ~loc:la raven, value))
                @ List.map st.chains ~f:(fun (field, raven) ->
                    ( ident ~loc:la raven,
                      List.Assoc.find_exn state.indices field ~equal:String.equal ))
                @ List.map st.pendings ~f:(fun p ->
                    ( ident ~loc:la p.pending_on,
                      List.Assoc.find_exn state.indices p.pending_field
                        ~equal:String.equal ))
              in
              begin match performs with
              | Some p ->
                  (* The action's state, which the history learns if a growing field
                     changes, supplies the fold witnesses. *)
                  let next, indices, appended =
                    next_state ctx st ~inv_params:st.params args opened p
                  in
                  let values = List.map next ~f:fst in
                  let grows =
                    List.exists2_exn st.fields next
                      ~f:(fun (_, _, _, _, grows) (_, changes) -> grows && changes)
                  in
                  let learn =
                    if grows then
                      [
                        lemma (member_name st "learn")
                          [
                            List.hd_exn args;
                            state_value st opened.values;
                            state_value st values;
                          ];
                      ]
                    else []
                  in
                  (* The state after the action, with its index maps. *)
                  let state =
                    {
                      values;
                      indices =
                        List.map opened.indices ~f:(fun (field, e) ->
                            ( field,
                              Option.value
                                (Option.bind
                                   (List.Assoc.find st.chains field ~equal:String.equal)
                                   ~f:(fun index ->
                                     List.Assoc.find indices index ~equal:String.equal))
                                ~default:e ));
                    }
                  in
                  let witnesses = witnesses state in
                  let after = state_of ~loc:l st (grown st values) in
                  ctx.positions <-
                    List.map appended ~f:(fun (field, e, k) ->
                        {
                          pos_inv = inv;
                          pos_field = field;
                          pos_element = e;
                          pos_snapshot = after;
                          pos_k = k;
                        })
                    @ ctx.positions;
                  (* The calls the action helps, committed in the state after it. *)
                  let helping =
                    match p.performed.helps with
                    | Some (field, key, _) -> begin
                        let env =
                          action_env ctx st st.params args opened.values p.bindings
                        in
                        match
                          ( List.find st.pendings ~f:(fun q ->
                                String.equal q.pending_field field),
                            formula env key,
                            views_after ctx st args values,
                            List.findi st.fields ~f:(fun _ (f, _, _, _, _) ->
                                String.equal f field) )
                        with
                        | Some pending, Ok c, Ok views, Some (i, _) ->
                            let on =
                              List.Assoc.find_exn opened.indices field ~equal:String.equal
                            in
                            let hc = R.Expr.var ~loc:la (name ~loc:la "hc") in
                            let helped =
                              R.Expr.set_compr ~loc:la
                                (R.Var.make ~loc:la (ident ~loc:la "hc")
                                   (R.Type.ref ~loc:la))
                                (R.Expr.binary ~loc:la Neq (R.Expr.index ~loc:la on hc) c)
                            in
                            [
                              lemma
                                (pending_name st pending "help")
                                (args @ [ c ]
                                @ List.map views ~f:(fun (_, _, value) -> value)
                                @ [ List.nth_exn opened.values i; on; helped ]);
                            ]
                        | _ -> []
                      end
                    | None -> []
                  in
                  if has_history st then
                    helping @ learn @ (snapshot st state :: fold ~witnesses ())
                  else fold ~witnesses ()
              | None when has_history st ->
                  snapshot st opened :: fold ~witnesses:(witnesses opened) ()
              | None ->
                  (* The heap determines the state without a history. *)
                  fold ()
              end
          | _ -> fold ()))

(** The known position of [e] in [field] of a snapshot of [inv]'s history, if any. *)
let known_position ctx inv field e =
  List.find ctx.positions ~f:(fun p ->
      String.equal p.pos_inv inv
      && String.equal p.pos_field field
      && R.Expr.alpha_equal p.pos_element e)

type position_join = {
  mutable merged : (position * R.Expr.t * R.Expr.t) list;
      (** The facts that arms learned, one for each entry, with the variables of their
          snapshots and positions. *)
  mutable decls : R.Stmt.t list;  (** Their declarations, before the branch. *)
  mutable learned : position list list;  (** The facts each arm learned. *)
}
(** The position facts of a branch's arms, joined after it. *)

(** Whether [p] and [q] are about the same entry. *)
let same_entry p q =
  String.equal p.pos_inv q.pos_inv
  && String.equal p.pos_field q.pos_field
  && R.Expr.alpha_equal p.pos_element q.pos_element

let new_join () = { merged = []; decls = []; learned = [] }

(** The statements at the end of an arm, which started with the facts [start], assigning
    the facts it learned to the variables of [join]. *)
let end_arm ctx join ~(start : position list) =
  let l = R.Loc.none in
  let learned =
    List.filter ctx.positions ~f:(fun p -> not (List.mem start p ~equal:phys_equal))
  in
  join.learned <- learned :: join.learned;
  List.concat_map learned ~f:(fun p ->
      let _, snapshot, k =
        match List.find join.merged ~f:(fun (q, _, _) -> same_entry p q) with
        | Some vars -> vars
        | None ->
            let st =
              List.find_exn ctx.shared.structures ~f:(fun st ->
                  String.equal st.invariant p.pos_inv)
            in
            let x = Names.fresh ctx.names "snapshot"
            and y = Names.fresh ctx.names "position" in
            join.decls <-
              join.decls
              @ R.Stmt.local ~loc:l ~ghost:true
                  ~typ:
                    (R.Type.named ~loc:l
                       (generated_module_member ~loc:l (module_name st "state") "T")
                       [])
                  (ident ~loc:l x)
              @ R.Stmt.local ~loc:l ~ghost:true ~typ:(R.Type.int ~loc:l) (ident ~loc:l y);
            let vars =
              (p, R.Expr.var ~loc:l (name ~loc:l x), R.Expr.var ~loc:l (name ~loc:l y))
            in
            join.merged <- vars :: join.merged;
            vars
      in
      [
        R.Stmt.assign ~loc:l [ snapshot ] (R.Stmt.expr_rhs p.pos_snapshot);
        R.Stmt.assign ~loc:l [ k ] (R.Stmt.expr_rhs p.pos_k);
      ])

(** The facts after a branch whose arms started with [start] and ended with [ends]: those
    that every arm kept, and those that every arm learned, in [join]'s variables. *)
let join_positions join ~(start : position list) (ends : position list list) =
  let kept =
    List.filter start ~f:(fun p ->
        List.for_all ends ~f:(fun e -> List.mem e p ~equal:phys_equal))
  in
  let learned =
    List.filter_map join.merged ~f:(fun (p, snapshot, k) ->
        Option.some_if
          (List.for_all join.learned ~f:(List.exists ~f:(same_entry p)))
          { p with pos_snapshot = snapshot; pos_k = k })
  in
  learned @ kept

(** The statements taking snapshots of the states of the open invariants with a history,
    which become the latest. *)
let take_snapshots ctx ~(at : Location.t) =
  let l = loc at in
  List.concat_map ctx.invariants ~f:(fun (inv, args) ->
      match
        ( List.find ctx.shared.structures ~f:(fun st -> String.equal st.invariant inv),
          List.Assoc.find ctx.opened inv ~equal:String.equal )
      with
      | Some st, Some opened when has_history st ->
          let snapshots =
            Option.value
              (List.Assoc.find ctx.snapshots inv ~equal:String.equal)
              ~default:[]
          in
          ctx.snapshots <-
            (inv, opened :: snapshots)
            :: List.Assoc.remove ctx.snapshots inv ~equal:String.equal;
          [
            R.Stmt.call ~loc:l
              (R.Expr.call ~loc:l
                 (qualified_name ~loc:l (member_name st "snapshot"))
                 [ List.hd_exn args; state_of ~loc:l st (grown st opened.values) ]);
          ]
      | _ -> [])

(** The snapshots taken on all of the paths [arms] ended with: those before the paths
    split. *)
let common_snapshots (arms : (string * opened list) list list) =
  (* The snapshots that [a] and [b], latest first, share. *)
  let shared a b =
    let rec go acc = function
      | x :: xs, y :: ys when phys_equal x y -> go (x :: acc) (xs, ys)
      | _ -> acc
    in
    go [] (List.rev a, List.rev b)
  in
  match arms with
  | [] -> []
  | first :: rest ->
      List.map first ~f:(fun (inv, snapshots) ->
          ( inv,
            List.fold rest ~init:snapshots ~f:(fun common arm ->
                shared common
                  (Option.value (List.Assoc.find arm inv ~equal:String.equal) ~default:[]))
          ))

(** [make], folding a predicate, preceded by setting the ghost field of a view to its new
    value, the last argument: the view changes with the state. *)
let with_views ctx make ~loc ~pred p args =
  match List.Assoc.find ctx.shared.views pred ~equal:String.equal with
  | Some field ->
      let structure = List.hd_exn args and value = List.last_exn args in
      R.Stmt.assign ~loc
        [
          R.Expr.field ~loc
            (anchored ctx ~loc ~pred structure)
            (qualified_name ~loc field);
        ]
        (R.Stmt.expr_rhs value)
      :: make ~loc ~pred p args
  | None -> make ~loc ~pred p args

(** The views of the open invariants, set to their values in the states after [p], and
    folded: the views are functions of the state. *)
let perform_views ctx ~(at : Location.t) (p : performing) =
  let l = loc at in
  all ctx.opened ~f:(fun (inv, opened) ->
      let structure =
        List.find ctx.shared.structures ~f:(fun st -> String.equal st.invariant inv)
      in
      let args = List.Assoc.find ctx.invariants inv ~equal:String.equal in
      match (structure, args) with
      | Some st, Some args ->
          let next, _, _ = next_state ctx st ~inv_params:st.params args opened p in
          let* views = views_after ctx st args (List.map next ~f:fst) in
          Ok
            (List.concat_map views ~f:(fun (pred, inputs, value) ->
                 let raven, _ = List.Assoc.find_exn ctx.preds pred ~equal:String.equal in
                 with_views ctx
                   (fun ~loc ~pred:_ p args -> [ R.Stmt.fold ~loc p args ])
                   ~loc:l ~pred (qualified_name ~loc:l raven) (inputs @ [ value ])))
      | _ -> Ok [])
  |> Result.map ~f:List.concat

(** The atomic that [t] denotes as the location of a step: one that an immutable record
    holds, as [q.head], or [t]'s value. *)
let atomic_of env (t : S.term) =
  let l = loc t.term_loc in
  match t.term_desc with
  | Tfield
      (({ term_desc = Tvar (Qid { pid_str = x; _ }); _ } as r), Qid { pid_str = label; _ })
    when Option.exists (List.Assoc.find env.var_types x ~equal:String.equal)
           ~f:(fun typ -> Option.is_some (atomic_in_record env.ctx typ label)) ->
      let* r = formula env r in
      Ok (R.Expr.field ~loc:l r (qualified_name ~loc:l label))
  | _ -> formula env t

(** The positions of [value], read from the atomic [atomic] at a step, in the latest
    snapshots: those of entries of fields owned by index that the invariants own the
    atomic holding. *)
let record_read ctx ~atomic value =
  List.iter ctx.opened ~f:(fun (inv, opened) ->
      match
        ( List.find ctx.shared.structures ~f:(fun st -> String.equal st.invariant inv),
          List.Assoc.find ctx.invariants inv ~equal:String.equal,
          List.Assoc.find ctx.snapshots inv ~equal:String.equal )
      with
      | Some st, Some args, Some (latest :: _) when has_history st ->
          let env = action_env ctx st st.params args opened.values [] in
          List.iter st.held ~f:(fun (location, field, position) ->
              match (atomic_of env location, formula env position) with
              | Ok held, Ok k when R.Expr.alpha_equal held atomic ->
                  ctx.positions <-
                    {
                      pos_inv = inv;
                      pos_field = field;
                      pos_element = value;
                      pos_snapshot = state_of ~loc:R.Loc.none st (grown st latest.values);
                      pos_k = k;
                    }
                    :: ctx.positions
              | _ -> ())
      | _ -> ())

(** The values of the parameters [params] of an action in [pattern], an argument of its
    step that the step's argument [actual] matches: a parameter itself, a position in a
    field owned by index, [s.cells.(k)], by the field's index map in [opened], or the
    arguments of a constructor. *)
let rec bind_params env st (opened : opened) params (pattern : S.term) actual =
  let l = R.Loc.none in
  let pattern = S.chain pattern in
  match spine pattern [] with
  | { term_desc = Tvar (Qid { pid_str = x; _ }); _ }, []
    when List.mem params x ~equal:String.equal ->
      [ (x, actual) ]
  | ( { term_desc = Tvar (Qid { pid_str = "([])"; _ }); _ },
      [
        {
          term_desc = Tfield ({ term_desc = Tvar (Qid { pid_str = s; _ }); _ }, Qid f);
          _;
        };
        { term_desc = Tvar (Qid { pid_str = k; _ }); _ };
      ] )
    when String.equal s st.state && List.mem params k ~equal:String.equal ->
      begin match List.Assoc.find opened.indices f.pid_str ~equal:String.equal with
      | Some index -> [ (k, R.Expr.index ~loc:l index actual) ]
      | None -> []
      end
  | { term_desc = Tvar (Qid { pid_str = c; _ }); _ }, args when Char.is_uppercase c.[0] ->
    begin
      let args = match args with [ { term_desc = Ttuple ts; _ } ] -> ts | _ -> args in
      match find_constructor env (S.Qid (S.mk_id ~loc:pattern.term_loc c)) with
      | Some (_, ctor) when List.length ctor.fields = List.length args ->
          List.concat
            (List.map2_exn args ctor.fields ~f:(fun a f ->
                 bind_params env st opened params a
                   (R.Expr.field ~loc:l actual (qualified_name ~loc:l f))))
      | _ -> []
    end
  | _ -> []

(** The actions that the step [op], at [location] with the arguments [args], may perform
    on the open invariants: those whose step is the same operation, at a location of the
    same type as [field] if known, with their parameters bound and the condition under
    which the step is theirs. *)
let step_performings ctx ~at ~op ~field ~location args =
  let l = loc at in
  List.concat_map ctx.opened ~f:(fun (inv, opened) ->
      let structure =
        List.find ctx.shared.structures ~f:(fun st -> String.equal st.invariant inv)
      in
      match (structure, List.Assoc.find ctx.invariants inv ~equal:String.equal) with
      | Some st, Some inv_args ->
          List.filter_map st.actions ~f:(fun a ->
              match a.step with
              | Some (o, Some loc_pattern :: patterns)
                when String.equal o op && List.length patterns = List.length args ->
                  let env bindings =
                    action_env ctx st st.params inv_args opened.values bindings
                  in
                  let bindings =
                    List.concat
                      (List.map2_exn patterns args ~f:(fun p actual ->
                           match p with
                           | Some p -> bind_params (env []) st opened a.params p actual
                           | None -> []))
                  in
                  let env = env bindings in
                  let same_field =
                    match term_type env loc_pattern with
                    | Some t ->
                        begin match field_of_type ctx ~at t "" with
                        | Ok (Some f) -> String.equal f field
                        | _ -> true
                        end
                    | None -> true
                  in
                  let condition =
                    let* location_pattern = atomic_of env loc_pattern in
                    let* equalities =
                      all (List.zip_exn patterns args) ~f:(fun (p, actual) ->
                          match p with
                          | Some p ->
                              let* p = formula env p in
                              Ok (Some (R.Expr.binary ~loc:l Eq p actual))
                          | None -> Ok None)
                    in
                    (* A position that a parameter gives is within its sequence. *)
                    let* bounds =
                      all (List.filter_opt patterns) ~f:(fun p ->
                          match spine (S.chain p) [] with
                          | ( { term_desc = Tvar (Qid { pid_str = "([])"; _ }); _ },
                              [
                                entries;
                                ({ term_desc = Tvar (Qid { pid_str = k; _ }); _ } as i);
                              ] )
                            when List.mem a.params k ~equal:String.equal ->
                              let* entries = formula env entries in
                              let* i = formula env i in
                              Ok
                                [
                                  R.Expr.binary ~loc:l Leq (R.Expr.int ~loc:l 0) i;
                                  R.Expr.binary ~loc:l Lt i
                                    (R.Expr.call ~loc:l
                                       (R.Name.make ~loc:l ~path:[ "Seq" ] "length")
                                       [ entries ]);
                                ]
                          | _ -> Ok [])
                    in
                    Ok
                      (List.fold
                         (List.filter_opt equalities @ List.concat bounds)
                         ~init:(R.Expr.binary ~loc:l Eq location_pattern location)
                         ~f:(R.Expr.binary ~loc:l And))
                  in
                  begin match (same_field, condition) with
                  | true, Ok condition -> Some ({ performed = a; bindings }, condition)
                  | _ -> None
                  end
              | _ -> None)
      | _ -> [])

(** The action named [a] of a structure, for [(*@ performs a *)]. *)
let named_action ctx (a : S.id) =
  let key = Option.value (ctx.proof_support.action_key a) ~default:a.pid_str in
  List.find_map ctx.shared.structures ~f:(fun st ->
      List.find st.actions ~f:(fun act -> String.equal act.action key))

(** The offset of the end of the step [e], where an annotation on it starts: that of its
    last argument, since a parenthesized step's location includes the parentheses, which
    may enclose the annotation, as in [Atomic.get (Atomic.get t (*@ ... *))]. *)
let step_end (e : Typedtree.expression) =
  match e.exp_desc with
  | Texp_apply (_, args) ->
      List.fold args ~init:e.exp_loc.loc_start.pos_cnum ~f:(fun last (_, arg) ->
          match arg with
          | Typedtree.Arg a -> Int.max last a.exp_loc.loc_end.pos_cnum
          | Omitted _ -> last)
  | _ -> e.exp_loc.loc_end.pos_cnum

(** The annotation saying how the atomic step [e] linearizes the function, if one follows
    it, as [Atomic.get t (*@ commit *)]. *)
let linearization ctx (e : Typedtree.expression) =
  match List.find ctx.linearizations ~f:(fun (anchor, _) -> anchor = step_end e) with
  | None -> Ok None
  | Some (_, a) when ctx.manual ->
      error a.loc
        "Automatic linearization annotations cannot be used in a manual function proof"
  | Some (_, a) -> Result.map (Annotation.linearization a) ~f:Option.some

(** The statements committing the open update [au] of a function that linearized: at once
    if it has no result, and otherwise at the end of the arm whose value is its result. *)
let commit_now (au : au) =
  if au.has_result then begin
    au.state <- Committing;
    Ok []
  end
  else begin
    au.state <- Committed;
    au.close Commit ~value:(R.Expr.tuple ~loc:(loc au.step) [])
  end

(** The open structure with a pending field among the invariants of the function, with its
    invariant's arguments and open state. *)
let open_pending_structure ctx =
  List.find_map ctx.opened ~f:(fun (inv, opened) ->
      match
        ( List.find ctx.shared.structures ~f:(fun st -> String.equal st.invariant inv),
          List.Assoc.find ctx.invariants inv ~equal:String.equal )
      with
      | Some st, Some args when not (List.is_empty st.pendings) -> Some (st, args, opened)
      | _ -> None)

(** The environment of a decision at a step whose result [value] matches [p], in the state
    [opened] of [st]. *)
let decision_env ?value_type ctx st (opened : opened) (p : S.pat) value =
  let env =
    bind (scope_env ctx) st.state
      (State
         (List.map2_exn st.fields opened.values ~f:(fun (f, _, _, t, _) v -> (f, (v, t)))))
  in
  match p.pat_desc with
  | Pid x ->
      let env = bind env x.pid_str (Value value) in
      Ok
        (Option.value_map value_type ~default:env ~f:(fun ty ->
             { env with var_types = (x.pid_str, ty) :: env.var_types }))
  | Pwild -> Ok env
  | _ -> unsupported p.pat_loc "A pattern other than a variable, before a choice,"

(** The statements of the step at [at] of the function with the update [au], whose result
    [value] matches [p]: the invariants are open, and [outcome] linearizes the function or
    leaves it to be helped, registered on a pending field. *)
let decide ?value_type ctx (au : au) ~(at : Location.t) ~value (p : S.pat)
    (outcome : S.outcome) =
  let l = loc at in
  let var x = R.Expr.var ~loc:l (name ~loc:l x) in
  let* st, args, opened =
    match open_pending_structure ctx with
    | Some found -> Ok found
    | None -> error at "A step that may wait without a structure with pending calls"
  in
  let* env = decision_env ?value_type ctx st opened p value in
  let snapshots = ctx.snapshots in
  let hc = Names.fresh ctx.names "registration" in
  let registered = Names.fresh ctx.names "registered" in
  let waiting = Names.fresh ctx.names "waiting" in
  (* The pending field the call may wait in. *)
  let rec waits (o : S.outcome) =
    match o with
    | Waits (field, _) -> Some field
    | Chooses (_, a, b) -> Option.first_some (waits a) (waits b)
    | Commits | Commits_with _ -> None
  in
  let* pending =
    match Option.map (waits outcome) ~f:(fun (field : S.term) -> field.term_desc) with
    | Some (Tfield (_, Qid f)) ->
        begin match
          List.find st.pendings ~f:(fun q -> String.equal q.pending_field f.pid_str)
        with
        | Some q -> Ok q
        | None -> error at (Printf.sprintf "%s is not a field of pending calls" f.pid_str)
        end
    | Some _ -> error at "A field of pending calls of the state, as s.waiting, to wait in"
    | None -> error at "A choice that never waits"
  in
  let i, _ =
    List.findi_exn st.fields ~f:(fun _ (f, _, _, _, _) ->
        String.equal f pending.pending_field)
  in
  let registrations = List.nth_exn opened.values i in
  (* Each way records the registrations it ends with, and whether it registered. *)
  let ends registrations waited =
    [
      R.Stmt.assign ~loc:l [ var waiting ] (R.Stmt.expr_rhs registrations);
      R.Stmt.assign ~loc:l
        [ var registered ]
        (R.Stmt.expr_rhs (R.Expr.bool ~loc:l waited));
    ]
  in
  let rec arm (o : S.outcome) =
    match o with
    | Commits_with t ->
        let* v = formula env t in
        let* commit = au.commit_only ~at ~value:v in
        let fold = use_invariants ctx ~at ~fold:true in
        ctx.snapshots <- snapshots;
        Ok (commit @ fold @ ends registrations false)
    | Commits -> unsupported at "Linearizing with the function's result, before a choice,"
    | Waits (_, key) ->
        let* key = formula env key in
        let on =
          List.Assoc.find_exn opened.indices pending.pending_field ~equal:String.equal
        in
        let added =
          R.Expr.call ~loc:l (name ~loc:l "++")
            [ registrations; R.Expr.set ~loc:l [ var hc ] ]
        in
        let next = List.mapi opened.values ~f:(fun j v -> if j = i then added else v) in
        let field f = qualified_name ~loc:l (pending_name st pending f) in
        let lemma f es =
          R.Stmt.call ~loc:l (R.Expr.call ~loc:l (qualified_name ~loc:l f) es)
        in
        let state values = state_of ~loc:l st (grown st values) in
        let inv = st.invariant in
        let after = { at with loc_start = at.loc_end } in
        ctx.origins :=
          {
            at = after;
            code = Fold;
            message = Printf.sprintf "The invariant %s may not hold after this step" inv;
            related = [];
          }
          :: !(ctx.origins);
        let _, raven_field, _, _, _ = List.nth_exn st.fields i in
        Ok
          ([
             R.Stmt.assign ~loc:l
               [ var hc ]
               (R.Stmt.new_rhs
                  [
                    (field "watched", Some key);
                    (field "linked", Some (R.Expr.bool ~loc:l false));
                    (field "token", Some au.token);
                    (field "retired", Some (R.Expr.bool ~loc:l false));
                  ]);
             R.Stmt.fold ~loc:l
               ~witnesses:
                 [
                   (ident ~loc:l "tok", au.token);
                   (ident ~loc:l "l", R.Expr.bool ~loc:l false);
                   (ident ~loc:l "r", R.Expr.bool ~loc:l false);
                 ]
               (qualified_name ~loc:l (pending_name st pending "registration"))
               (var hc :: args);
             lemma (member_name st "learn")
               [ List.hd_exn args; state opened.values; state next ];
             lemma (member_name st "snapshot") [ List.hd_exn args; state next ];
             R.Stmt.fold ~loc:(loc after)
               ~witnesses:
                 [
                   (ident ~loc:l raven_field, added);
                   (ident ~loc:l pending.pending_on, R.Expr.update ~loc:l on (var hc) key);
                 ]
               (qualified_name ~loc:l inv) args;
           ]
          @ ends added true)
    | Chooses (c, a, b) ->
        let* c = formula env c in
        let* a = arm a in
        let* b = arm b in
        Ok [ R.Stmt.if_ ~loc:l c a b ]
  in
  let* stmts = arm outcome in
  let j = i in
  (* The latest snapshot, on either path: the state with the registrations each ended
     with. *)
  let merged =
    {
      opened with
      values = List.mapi opened.values ~f:(fun k v -> if k = j then var waiting else v);
    }
  in
  ctx.snapshots <-
    ( st.invariant,
      merged
      :: Option.value
           (List.Assoc.find snapshots st.invariant ~equal:String.equal)
           ~default:[] )
    :: List.Assoc.remove snapshots st.invariant ~equal:String.equal;
  au.state <-
    Registered
      {
        registration = var hc;
        registered = var registered;
        pending_inv = st.invariant;
        pending;
      };
  au.step <- at;
  let local x typ = R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x) in
  let _, _, waiting_typ, _, _ = List.nth_exn st.fields j in
  Ok
    (local hc (R.Type.ref ~loc:l)
    @ local registered (R.Type.bool ~loc:l)
    @ local waiting waiting_typ
    @ [ R.Stmt.ghost_block ~loc:l stmts ])

(** The statements of the step at [at] that collects the result of the function with the
    update [au], left to be helped as [r] says, if its result [value] matches [p]:
    committing with [result] if nobody helped it, and retiring the registration. *)
let collect ctx (au : au) (r : registered) ~(at : Location.t) ~value (p : S.pat) result =
  let l = loc at in
  let var x = R.Expr.var ~loc:l (name ~loc:l x) in
  let* st, args, _ =
    match open_pending_structure ctx with
    | Some found -> Ok found
    | None ->
        error at "A step that collects a result without a structure with pending calls"
  in
  let env = scope_env ctx in
  let* matches, _ = spec_pattern env p value in
  let* result = formula env result in
  let* commit = au.commit_only ~at ~value:result in
  let linked = Names.fresh ctx.names "linked" in
  let registration = qualified_name ~loc:l (pending_name st r.pending "registration") in
  let retired = qualified_name ~loc:l (pending_name st r.pending "retired") in
  au.state <- Committed;
  au.step <- at;
  Ok
    [
      R.Stmt.ghost_block ~loc:l
        [
          R.Stmt.if_ ~loc:l r.registered
            (R.Stmt.local ~loc:l ~ghost:true ~typ:(R.Type.bool ~loc:l)
               (ident ~loc:l linked)
            @ [
                R.Stmt.unfold ~loc:l
                  ~witnesses:[ (ident ~loc:l linked, var "l") ]
                  registration (r.registration :: args);
              ]
            @ (match matches with
              | Some c -> [ R.Stmt.if_ ~loc:l c commit [] ]
              | None -> commit)
            @ [
                R.Stmt.assign ~loc:l
                  [ R.Expr.field ~loc:l r.registration retired ]
                  (R.Stmt.expr_rhs (R.Expr.bool ~loc:l true));
                R.Stmt.fold ~loc:l
                  ~witnesses:
                    [
                      (ident ~loc:l "tok", au.token);
                      (ident ~loc:l "l", var linked);
                      (ident ~loc:l "r", R.Expr.bool ~loc:l true);
                    ]
                  registration (r.registration :: args);
              ])
            [];
        ];
    ]

(** The statements of [access], an atomic step, inside the atomic update of a function
    with an atomic contract that has not linearized yet. The step linearizes the function
    as [how] says: always, never, if it is a [compare_and_set] that succeeds, or if it is
    a read whose value has a constructor. *)
let linearize ?step ?value ?access_type ctx ~at
    (how :
      [ `Commit | `Abort | `Cas | `Returning of string | `Decide of S.pat * S.outcome ])
    access =
  let annotation =
    List.Assoc.find ctx.access_proofs
      (at.Location.loc_start.pos_cnum, at.loc_end.pos_cnum)
      ~equal:Poly.equal
  in
  if ctx.manual then
    match (annotation, value, access_type) with
    | None, _, _ -> Ok access
    | Some annotation, Some result, Some result_type ->
        access_proof ctx annotation ~result_type (fun _ -> Ok (access, result, []))
    | Some annotation, _, _ ->
        error annotation.loc "This operation does not support an access proof"
  else if Option.is_some annotation then
    error (Option.value_exn annotation).loc "Ghost.scope requires a manual function proof"
  else
    let l = loc at in
    (* The actions that the step may perform, once the invariants are open. *)
    let performings () =
      match step with
      | Some (op, field, location, args, _) ->
          step_performings ctx ~at ~op ~field ~location args
      | None -> []
    in
    let around access =
      let opening = use_invariants ctx ~at ~fold:false in
      match (performings (), step) with
      | [], _ | _, None -> opening @ access @ use_invariants ctx ~at ~fold:true
      | performings, Some (_, _, _, _, result) ->
          (* If the step succeeds, it performs the action whose step it is, or changes
           nothing. The state before it is the latest snapshot after it on every path. *)
          let snapshot = take_snapshots ctx ~at in
          let snapshots = ctx.snapshots in
          let close ?performs ?no_action () =
            ctx.snapshots <- snapshots;
            use_invariants ?performs ?no_action ctx ~at ~fold:true
          in
          let unchanged = close ~no_action:true () in
          let performed =
            List.fold_right performings ~init:unchanged ~f:(fun (p, condition) rest ->
                [ R.Stmt.if_ ~loc:l condition (close ~performs:p ()) rest ])
          in
          let failed = close () in
          ctx.snapshots <- snapshots;
          opening @ access @ snapshot
          @ [ R.Stmt.if_ ~loc:l result [ R.Stmt.ghost_block ~loc:l performed ] failed ]
    in
    match (ctx.au, how, value) with
    | None, `Decide _, _ ->
        error at "A choice of how to linearize outside an atomic function"
    | Some au, `Decide (p, o), Some value ->
        begin match (au.state, o) with
        | Pending, _ ->
            (* The invariants open, the update not: the step decides. *)
            let opening = use_invariants ctx ~at ~fold:false in
            let* decision = decide ?value_type:access_type ctx au ~at ~value p o in
            Ok (opening @ access @ decision)
        | Registered r, Commits_with result ->
            let opening = use_invariants ctx ~at ~fold:false in
            let* collected = collect ctx au r ~at ~value p result in
            Ok (opening @ access @ collected @ use_invariants ctx ~at ~fold:true)
        | _ ->
            error at
              "Caravan cannot tell whether the function has linearized before this step"
        end
    | Some _, `Decide _, None -> error at "Only a read can linearize by its value"
    | None, _, _ -> Ok (around access)
    | Some au, ((`Commit | `Abort | `Cas | `Returning _) as how), _ ->
        begin match au.state with
        | Committed -> Ok (around access)
        | Registered _ ->
            error at
              "This function waits to be helped: the next step collects its result, as \
               (*@ returning Nil -> commit true *)"
        | Committing | On_cas | On_read _ | Partly | Unknown ->
            error at
              "Caravan cannot tell whether the function has linearized before this step"
        | Pending ->
            let* opening, values = au.open_ ~at ~unfold:true in
            au.values <- values;
            au.step <- at;
            au.read_results <- [];
            let* closing =
              match how with
              | `Abort ->
                  au.state <- Pending;
                  au.close Abort ~value:(R.Expr.tuple ~loc:(loc at) [])
              | `Commit -> commit_now au
              | `Cas ->
                  au.state <- On_cas;
                  (* The action that the step performs if it succeeds, which linearizes the
                   function. *)
                  let linearizing =
                    List.filter (performings ()) ~f:(fun (p, _) ->
                        List.mem p.performed.linearizes au.role ~equal:Ident.same)
                  in
                  begin match (linearizing, au.performing) with
                  | _, Some _ | [], None -> Ok []
                  | [ (p, condition) ], None ->
                      au.performing <- Some (p, Some condition);
                      Ok []
                  | _ :: _ :: _, None ->
                      error at
                        "This step may perform several actions that linearize the \
                         function"
                  end
              | `Returning c ->
                  au.state <- On_read c;
                  Ok []
            in
            Ok (opening @ access @ closing)
        end

(** The statements at the start of an arm of a branch on the result of the step that left
    the update open: committing if the step linearized the function there, as [commits]
    says, and aborting otherwise. *)
let enter_arm ctx ~(commits : bool option) =
  match ctx.au with
  | Some ({ state = On_cas | On_read _; _ } as au) ->
      begin match commits with
      | Some true -> commit_now au
      | Some false ->
          au.state <- Pending;
          au.close Abort ~value:(R.Expr.tuple ~loc:(loc au.step) [])
      | None ->
          au.state <- Unknown;
          Ok []
      end
  | _ -> Ok []

(** The statements at the end of an arm whose value [v] is the function's result: the
    commit, if the function linearized in the arm. *)
let finish_arm ctx ~tail v =
  match ctx.au with
  | Some ({ state = Committing; _ } as au) when tail ->
      au.state <- Committed;
      au.close Commit ~value:v
  | _ -> Ok []

(** The state of the atomic update after two branches. *)
let join_au a b =
  match (a, b) with
  | _ when Poly.equal a b -> a
  | (Pending | Committed | Partly), (Pending | Committed | Partly) -> Partly
  | _ -> Unknown

let au_state ctx = Option.map ctx.au ~f:(fun au -> au.state)

let set_au_state ctx = function
  | Some state -> Option.iter ctx.au ~f:(fun au -> au.state <- state)
  | None -> ()

(** The atomic update before a branch, for each arm to start from. *)
let au_snapshot ctx =
  ( Option.map ctx.au ~f:(fun au -> (au.state, au.step, au.values, au.performing)),
    ctx.opened,
    (ctx.snapshots, ctx.positions) )

let restore_au ctx (au_state, opened, (snapshots, positions)) =
  ctx.opened <- opened;
  ctx.snapshots <- snapshots;
  ctx.positions <- positions;
  match (ctx.au, au_state) with
  | Some au, Some (state, step, values, performing) ->
      au.state <- state;
      au.step <- step;
      au.values <- values;
      au.performing <- performing
  | _ -> ()

(** Whether [c] is the result of a [compare_and_set], [Some false] if its negation. *)
let rec cas_polarity ctx (c : Typedtree.expression) =
  match c.exp_desc with
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, args) ->
      begin match (atomic_name path, unop_of_path path, args) with
      | Some "compare_and_set", _, _ -> Some true
      | _, Some `Not, [ (_, Arg a) ] -> Option.map (cas_polarity ctx a) ~f:not
      | _ -> None
      end
  | Texp_ident (Pident id, _, _) ->
      Option.bind ctx.au ~f:(fun au ->
          List.Assoc.find au.cas_results (Ident.unique_name id) ~equal:String.equal)
  | _ -> None

(** Whether [e] is the value of the last read. *)
let is_read_value ctx (e : Typedtree.expression) =
  match e.exp_desc with
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _) ->
      Option.equal String.equal (atomic_name path) (Some "get")
  | Texp_ident (Pident id, _, _) ->
      Option.exists ctx.au ~f:(fun au ->
          List.mem au.read_results (Ident.unique_name id) ~equal:String.equal)
  | _ -> false

(** For each of [cases], of a match on the value of a read that linearizes the function if
    the value has the constructor [c], whether the case's value has it; [None] if that is
    not clear. *)
let case_commits c (patterns : Typedtree.pattern list) =
  let rec ctor (p : Typedtree.pattern) =
    match p.pat_desc with
    | Tpat_construct (_, cstr, _, _) -> Some cstr.cstr_name
    | Tpat_alias (p, _, _, _, _) -> ctor p
    | _ -> None
  in
  let _, commits =
    List.fold_map patterns ~init:false ~f:(fun seen p ->
        match ctor p with
        | Some name -> (seen || String.equal name c, Some (String.equal name c))
        | None -> (seen, if seen then Some false else None))
  in
  commits

let no_loop_before_linearizing ctx ~at =
  match au_state ctx with
  | None | Some Committed -> Ok ()
  | Some _ ->
      unsupported at "A loop in a function with an atomic contract, before it linearizes,"

(** The statements declaring arbitrary values for the ghost fields of the views that an
    allocation of [fields] allocates, and these fields with their values: a view's value
    is set when the structure's invariant is established. *)
let view_allocation ctx ~loc:l (fields : string list) =
  let views =
    List.concat_map fields ~f:(fun field ->
        Option.value
          (List.Assoc.find ctx.shared.anchors field ~equal:String.equal)
          ~default:[])
  in
  let allocated =
    List.map views ~f:(fun (view, typ, init) ->
        match init with
        | Some init -> ([], (qualified_name ~loc:l view, Some init))
        | None ->
            let x = Names.fresh ctx.names "view" in
            ( R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x),
              (qualified_name ~loc:l view, Some (R.Expr.var ~loc:l (name ~loc:l x))) ))
  in
  (List.concat_map allocated ~f:fst, List.map allocated ~f:snd)

let allocation_initializers ctx (e : Typedtree.expression) =
  match
    List.Assoc.find ctx.initializations
      (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum)
      ~equal:Poly.equal
  with
  | None -> Ok []
  | Some annotation ->
      let* initializers = Annotation.initializes annotation in
      ghost_initializers (scope_env ctx) ~owner:e.exp_type initializers

(** The statements evaluating [e], and the value of [e] after them; [tail] if the value is
    the function's result. *)
let rec expr ?(tail = false) ?(continue_state = false) ?(keep_scope = false)
    (ctx : context) (e : Typedtree.expression) :
    (R.Stmt.t list * R.Expr.t, error) Result.t =
  let incoming = ctx.proof_state and covered = ctx.return_covered in
  let incoming_names = ctx.names.scope in
  let key = (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum) in
  let adapter = List.Assoc.find ctx.return_proofs key ~equal:Poly.equal in
  let* () =
    match adapter with
    | Some a when not tail ->
        error a.loc "Ghost.returns must follow a normal tail expression"
    | Some a when covered ->
        error a.loc "This return path has more than one Ghost.returns annotation"
    | _ -> Ok ()
  in
  ctx.return_covered <- covered || Option.is_some adapter;
  let tail_container =
    match e.exp_desc with
    | Texp_let _ | Texp_sequence _ | Texp_match _ -> true
    | Texp_ifthenelse (_, _, Some _) -> true
    | _ -> false
  in
  let* () =
    if
      tail && (not ctx.return_covered) && (not tail_container)
      && not (List.is_empty ctx.ghost_returns)
    then error e.exp_loc "A normal return with ghost results needs Ghost.returns"
    else Ok ()
  in
  let* statements, value = expr_body ~tail ~keep_scope ctx e in
  let* finish =
    match adapter with
    | None -> Ok []
    | Some a -> return_proof ctx a ~result_type:e.exp_type ~result:value
  in
  let* stateful = stateful_access ctx.access_proofs e in
  if not (continue_state && stateful) then ctx.proof_state <- incoming;
  if not keep_scope then ctx.names.scope <- incoming_names;
  ctx.return_covered <- covered;
  Ok (statements @ finish, value)

and expr_body ~tail ~keep_scope (ctx : context) (e : Typedtree.expression) :
    (R.Stmt.t list * R.Expr.t, error) Result.t =
  let at = e.exp_loc in
  let l = loc at in
  match e.exp_desc with
  | Texp_ident (Pident id, _, _) -> (
      match Names.find ctx.names id with
      | Some x -> Ok ([], R.Expr.var ~loc:l (name ~loc:l x))
      | None -> unsupported at "A function used as a value")
  | Texp_ident (path, _, _) -> (
      let* path = Source.normalize_value_path e.exp_env ~at path in
      match Path_bindings.member ctx.libraries path with
      | Some member -> Ok ([], R.Expr.call ~loc:l (Qualified_name.raven ~loc:l member) [])
      | None ->
          begin match stdlib_name path with
          | Some "max_int" -> Ok ([], R.Expr.int ~loc:l Prelude.max_int)
          | Some "min_int" -> Ok ([], R.Expr.int ~loc:l Prelude.min_int)
          | _ -> unsupported at "This identifier"
          end)
  | Texp_constant (Const_int n) -> Ok ([], R.Expr.int ~loc:l n)
  | Texp_constant _ -> unsupported at "This constant"
  | Texp_construct ({ txt = Lident "true"; _ }, _, []) -> Ok ([], R.Expr.bool ~loc:l true)
  | Texp_construct ({ txt = Lident "false"; _ }, _, []) ->
      Ok ([], R.Expr.bool ~loc:l false)
  | Texp_construct ({ txt = Lident "()"; _ }, _, []) -> Ok ([], unit_value ~loc:l)
  | Texp_construct (_, cstr, args) ->
      begin match Datatypes.find_cstr ctx.types cstr with
      | None -> unsupported at "This constructor"
      | Some (d, c) ->
          let* stmts, args = operands ctx args in
          Ok (stmts, R.Expr.call ~loc:l (Datatypes.ctor_name ~loc:l d c) args)
      end
  | Texp_tuple components ->
      let* stmts, components = operands ctx (List.map components ~f:snd) in
      Ok (stmts, R.Expr.tuple ~loc:l components)
  | Texp_record { fields; extended_expression = None; _ } ->
      let fields = Array.to_list fields in
      let* values =
        all fields ~f:(fun (label, def) ->
            match (def : Typedtree.record_label_definition) with
            | Overridden (_, e) -> Ok (label, e)
            | Kept _ -> unsupported at "This record")
      in
      let* stmts, args = operands ctx (List.map values ~f:snd) in
      let label, _ = List.hd_exn fields in
      begin match Datatypes.find_label ctx.types label with
      | Some { heap = Some _; _ } ->
          let* typ = typ ctx ~at e.exp_type in
          let* fields =
            all values ~f:(fun (label, _) ->
                let* field = field_of_label ctx ~at label in
                Ok (fst (Option.value_exn field)))
          in
          let x = Names.fresh ctx.names "tmp" in
          let views, view_args = view_allocation ctx ~loc:l fields in
          let* explicit = allocation_initializers ctx e in
          let init =
            R.Stmt.new_rhs
              (List.map2_exn fields args ~f:(fun f v -> (qualified_name ~loc:l f, Some v))
              @ view_args @ explicit)
          in
          Ok
            ( stmts @ views @ R.Stmt.local ~loc:l ~typ ~init (ident ~loc:l x),
              R.Expr.var ~loc:l (name ~loc:l x) )
      | Some ({ ctors = [ c ]; _ } as d) ->
          Ok (stmts, R.Expr.call ~loc:l (Datatypes.ctor_name ~loc:l d c) args)
      | _ -> unsupported at "This record"
      end
  | Texp_record _ -> unsupported at "A record copied with changes"
  | Texp_field (record, _, label) -> begin
      let* stmts, v = expr ctx record in
      let* field = field_of_label ctx ~at label in
      match field with
      | Some (field, true) ->
          let* reading, value = ordinary_read ctx ~at ~field ~elt:e.exp_type v in
          Ok (stmts @ reading, value)
      | Some (field, false) ->
          let value = R.Expr.field ~loc:l v (qualified_name ~loc:l field) in
          if is_int e.exp_type then
            let x = Names.fresh ctx.names "tmp" in
            Ok
              ( stmts
                @ R.Stmt.local ~loc:l ~typ:(R.Type.int ~loc:l)
                    ~init:(R.Stmt.expr_rhs value) (ident ~loc:l x)
                @ assume_in_range ~loc:l e.exp_type x,
                R.Expr.var ~loc:l (name ~loc:l x) )
          else Ok (stmts, value)
      | None -> unsupported at "This field"
    end
  | Texp_setfield (record, _, label, value) -> begin
      let* value_stmts, value = expr ctx value in
      let* record_stmts, record = expr ctx record in
      let* field = field_of_label ctx ~at label in
      match field with
      | Some (field, true) ->
          let* writing = ordinary_write ctx ~at ~field ~elt:label.lbl_arg record value in
          Ok (value_stmts @ record_stmts @ [ writing ], unit_value ~loc:l)
      | _ -> unsupported at "This field"
    end
  | Texp_match (scrutinee, cases, [], partial) ->
      let read = is_read_value ctx scrutinee in
      let* scrutinee_stmts, v = expr ctx scrutinee in
      (* The cases read the scrutinee repeatedly, so it is named unless it is a variable. *)
      let* naming, v =
        match scrutinee.exp_desc with
        | Texp_ident (Pident _, _, _) -> Ok ([], v)
        | _ ->
            let* typ = typ ctx ~at:scrutinee.exp_loc scrutinee.exp_type in
            let x = Names.fresh ctx.names "scrutinee" in
            Ok
              ( R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs v) (ident ~loc:l x),
                R.Expr.var ~loc:l (name ~loc:l x) )
      in
      let* cases =
        all cases ~f:(fun (c : Typedtree.computation Typedtree.case) ->
            match (Typedtree.split_pattern c.c_lhs, c.c_guard) with
            | (Some p, None), None -> Ok (p, c.c_rhs)
            | _, Some guard -> unsupported guard.exp_loc "A guard"
            | _ -> unsupported c.c_lhs.pat_loc "An exception case")
      in
      let total = match partial with Total -> true | Partial -> false in
      (* A match on the value of a read that left the atomic update open closes it. *)
      let commits =
        match au_state ctx with
        | Some (On_read c) when read -> Some (case_commits c (List.map cases ~f:fst))
        | _ -> None
      in
      let* stmts =
        branch ctx e (fun target ->
            match_cases ?commits ~tail ctx ~at v cases ~total target)
      in
      Ok (scrutinee_stmts @ naming @ fst stmts, snd stmts)
  | Texp_match (_, _, _ :: _, _) -> unsupported at "An effect handler"
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, args) ->
      let* args = plain_args ~at args in
      apply ctx e path args
  | Texp_apply _ -> unsupported at "This application"
  | Texp_ifthenelse (c, e1, e2) ->
      let polarity = cas_polarity ctx c in
      let* c_stmts, c = expr ctx c in
      let* stmts =
        branch ctx e (fun target -> conditional ctx ~at ?polarity ~tail c e1 e2 target)
      in
      Ok (c_stmts @ fst stmts, snd stmts)
  | Texp_let (_, [ { vb_pat = { pat_desc = Tpat_var (id, _, _); _ }; _ } ], rest)
    when Path_bindings.mem ctx.functions (Path.Pident id) ->
      (* A local function, lifted to the top level. *)
      expr ~tail ~keep_scope ctx rest
  | Texp_let (Nonrecursive, bindings, body) ->
      (* The bound expressions are evaluated before any of their variables is bound. *)
      let* evaluated =
        all bindings ~f:(fun (vb : Typedtree.value_binding) ->
            let polarity = cas_polarity ctx vb.vb_expr in
            let read = is_read_value ctx vb.vb_expr in
            let* stmts, v =
              expr ~continue_state:(List.length bindings = 1) ctx vb.vb_expr
            in
            begin match (ctx.au, polarity, vb.vb_pat.pat_desc) with
            | Some au, Some p, Tpat_var (id, _, _) ->
                au.cas_results <- (Ident.unique_name id, p) :: au.cas_results
            | Some au, None, Tpat_var (id, _, _) when read ->
                au.read_results <- Ident.unique_name id :: au.read_results
            | _ -> ()
            end;
            Ok (vb, stmts, v))
      in
      let* defs =
        all evaluated ~f:(fun ((vb : Typedtree.value_binding), _, v) ->
            let* reading, cond, binds = pattern ctx vb.vb_pat v in
            match cond with
            | Some _ ->
                unsupported vb.vb_pat.pat_loc "A refutable pattern in a let binding"
            | None ->
                let* defs =
                  all binds ~f:(fun (id, value, t) ->
                      let* typ = typ ctx ~at t in
                      let x = Names.bind ~typ:t ctx.names id in
                      Ok
                        (R.Stmt.local ~loc:l ~const:true ~typ
                           ~init:(R.Stmt.expr_rhs value) (ident ~loc:l x)
                        @ assume_in_range ~loc:l t x))
                in
                Ok (reading @ List.concat defs))
      in
      let last = List.last_exn bindings in
      let* ghost =
        ghost ctx ~after:last.vb_expr.exp_loc.loc_end ~before:body.exp_loc.loc_start
      in
      let* body_stmts, body = expr ~tail ~keep_scope ctx body in
      Ok
        ( List.concat_map evaluated ~f:(fun (_, stmts, _) -> stmts)
          @ List.concat defs @ ghost @ body_stmts,
          body )
  | Texp_let (Recursive, _, _) -> unsupported at "A local recursive function"
  | Texp_sequence (e1, e2) ->
      let* stmts1, _ = expr ~continue_state:true ctx e1 in
      let* ghost = ghost ctx ~after:e1.exp_loc.loc_end ~before:e2.exp_loc.loc_start in
      let* stmts2, v = expr ~tail ~keep_scope ctx e2 in
      Ok (stmts1 @ ghost @ stmts2, v)
  | Texp_while (cond, body) ->
      let* () = no_loop_before_linearizing ctx ~at in
      let* spec = loop_spec ctx ~after:cond.exp_loc body in
      let* c_stmts, c = expr ctx cond in
      let x = Names.fresh ctx.names "continue" in
      (* A condition that needs statements, as reads, is evaluated before the loop and at the
         end of each iteration, into [x]; the invariant relates [x] to the values it owns,
         if the condition can be expressed in them. *)
      let relation reads =
        if List.is_empty c_stmts then Ok None
        else
          match pure ~reads ctx ~funcs:Path_bindings.empty [] cond with
          | Ok c ->
              Ok (Some (R.Expr.binary ~loc:l Eq (R.Expr.var ~loc:l (name ~loc:l x)) c))
          | Error _ -> Ok None
      in
      let* invariants = loop_invariants ctx ~at spec ~relation in
      let* body_stmts, _ = expr ctx body in
      if List.is_empty c_stmts then
        Ok ([ R.Stmt.while_ ~loc:l ~invariants c body_stmts ], unit_value ~loc:l)
      else
        let target = (x, l) in
        let* c_stmts', c' = expr ctx cond in
        Ok
          ( c_stmts
            @ R.Stmt.local ~loc:l ~const:false ~typ:(R.Type.bool ~loc:l) (ident ~loc:l x)
            @ [
                assign target c;
                R.Stmt.while_ ~loc:l ~invariants
                  (R.Expr.var ~loc:l (name ~loc:l x))
                  (body_stmts @ c_stmts' @ [ assign target c' ]);
              ],
            unit_value ~loc:l )
  | Texp_for (id, _, lo, hi, direction, body) ->
      let* () = no_loop_before_linearizing ctx ~at in
      let* spec = loop_spec ctx ~after:hi.exp_loc body in
      let* lo_stmts, lo = expr ctx lo in
      let* hi_stmts, hi = expr ctx hi in
      let int = R.Type.int ~loc:l in
      (* A bound, evaluated once into a variable, which the invariant says it equals, as the
         value is an expression of immutable variables. *)
      let bound base v =
        let x = Names.fresh ctx.names base in
        let var = R.Expr.var ~loc:l (name ~loc:l x) in
        ( R.Stmt.local ~loc:l ~typ:int ~init:(R.Stmt.expr_rhs v) (ident ~loc:l x),
          var,
          R.Spec.make (R.Expr.binary ~loc:l Eq var v) )
      in
      let lo_def, lo, lo_value = bound "first" lo in
      let hi_def, hi, hi_value = bound "last" hi in
      let i = Names.bind ~typ:Predef.type_int ctx.names id in
      let iv = R.Expr.var ~loc:l (name ~loc:l i) in
      let* invariants =
        loop_invariants ~counter:i ctx ~at spec ~relation:(fun _ -> Ok None)
      in
      let bin op a b = R.Expr.binary ~loc:l op a b in
      let one = R.Expr.int ~loc:l 1 in
      let test, step, beyond =
        match direction with
        | Upto -> (bin Leq iv hi, bin Plus iv one, bin Plus hi one)
        | Downto -> (bin Geq iv hi, bin Minus iv one, bin Minus hi one)
      in
      (* The counter stays between the first value and one beyond the last. *)
      let range =
        match direction with
        | Upto -> bin And (bin Leq lo iv) (bin Or (bin Leq iv beyond) (bin Eq iv lo))
        | Downto -> bin And (bin Geq lo iv) (bin Or (bin Geq iv beyond) (bin Eq iv lo))
      in
      let* body_stmts, _ = expr ctx body in
      Ok
        ( lo_stmts @ hi_stmts @ lo_def @ hi_def
          @ R.Stmt.local ~loc:l ~const:false ~typ:int ~init:(R.Stmt.expr_rhs lo)
              (ident ~loc:l i)
          @ [
              R.Stmt.while_ ~loc:l
                ~invariants:(R.Spec.make range :: lo_value :: hi_value :: invariants)
                test
                (body_stmts @ [ assign (i, l) step ]);
            ],
          unit_value ~loc:l )
  | Texp_assert (c, _) ->
      let* stmts, c = expr ctx c in
      Ok (stmts @ [ R.Stmt.assert_ ~loc:l (R.Spec.make c) ], unit_value ~loc:l)
  | _ -> unsupported at "This expression"

(** The application of the function at [path] to [args], in [e]. *)
and apply ctx (e : Typedtree.expression) (path : Path.t)
    (args : Typedtree.expression list) =
  let at = e.exp_loc in
  let l = loc at in
  let contents (r : Typedtree.expression) =
    match Datatypes.desc ctx.types r.exp_type with
    | Tconstr (_, [ elt ], _) -> ref_field ctx ~at elt
    | _ -> unsupported at "This reference"
  in
  (* The value of the field [field] of the reference [r], read into a variable. *)
  let read r field typ_of = ordinary_read ctx ~at ~field ~elt:typ_of r in
  match (stdlib_name path, args) with
  | _ when Option.is_some (atomic_name path) ->
      atomic ctx e (Option.value_exn (atomic_name path)) args
  | Some "ref", [ v ] ->
      let* field = ref_field ctx ~at v.exp_type in
      let* stmts, v = expr ctx v in
      let x = Names.fresh ctx.names "tmp" in
      let views, view_args = view_allocation ctx ~loc:l [ field ] in
      let* explicit = allocation_initializers ctx e in
      let init =
        R.Stmt.new_rhs ((qualified_name ~loc:l field, Some v) :: (view_args @ explicit))
      in
      Ok
        ( stmts @ views
          @ R.Stmt.local ~loc:l ~typ:(R.Type.ref ~loc:l) ~init (ident ~loc:l x),
          R.Expr.var ~loc:l (name ~loc:l x) )
  | Some "!", [ r ] ->
      let* field = contents r in
      let* stmts, r = expr ctx r in
      let* reading, v = read r field e.exp_type in
      Ok (stmts @ reading, v)
  | Some ":=", [ r; v ] ->
      let* field = contents r in
      let elt = v.exp_type in
      let* v_stmts, v = expr ctx v in
      let* r_stmts, r = expr ctx r in
      let* writing = ordinary_write ctx ~at ~field ~elt r v in
      Ok (v_stmts @ r_stmts @ [ writing ], unit_value ~loc:l)
  | Some (("incr" | "decr") as op), [ r ] ->
      let* field = contents r in
      let* stmts, r = expr ctx r in
      let int_type = Predef.type_int in
      let* reading, v = read r field int_type in
      let binop : R.Expr.binop = if String.equal op "incr" then Plus else Minus in
      let v' = R.Expr.binary ~loc:l binop v (R.Expr.int ~loc:l 1) in
      let what = if String.equal op "incr" then "increment" else "decrement" in
      let* writing = ordinary_write ctx ~at ~field ~elt:int_type r v' in
      Ok (stmts @ reading @ [ no_overflow ctx ~at what v'; writing ], unit_value ~loc:l)
  | _ -> apply_operator ctx e path args

(** The application of [Atomic.op] to [args], in [e]. *)
and atomic ctx (e : Typedtree.expression) op (args : Typedtree.expression list) =
  let at = e.exp_loc in
  let l = loc at in
  let element (t : Types.type_expr) =
    match Datatypes.desc ctx.types t with
    | Tconstr (_, [ elt ], _) -> Ok elt
    | _ -> unsupported at "This atomic"
  in
  (* How the step linearizes the function: as its annotation says, or by default. *)
  let* annotation = linearization ctx e in
  let how default =
    match (annotation, default) with
    | None, _ -> Ok default
    | Some (S.Performs a), _ ->
        begin match named_action ctx a with
        | Some performed ->
            Option.iter ctx.au ~f:(fun au ->
                au.performing <- Some ({ performed; bindings = [] }, None));
            Ok default
        | None -> error a.pid_loc (Printf.sprintf "There is no action %s" a.pid_str)
        end
    | Some S.Commit, _ -> Ok `Commit
    | Some (Returning ({ pat_desc = Pconstr (Qid c, _); _ }, Commits)), `Abort ->
        Ok (`Returning c.pid_str)
    | Some (Returning (p, Commits)), `Abort ->
        unsupported p.pat_loc "A pattern other than a constructor, after returning,"
    | Some (Returning (p, o)), `Abort -> Ok (`Decide (p, o))
    | Some (Returning (p, _)), _ ->
        error p.pat_loc "Only a read can linearize by its value"
  in
  (* The result of [f] applied to the atomic and [args], in a variable, a step that
     linearizes the function by default as [default] says. *)
  let result ?(default = `Commit) ?op f atomic args =
    let* typ = typ ctx ~at e.exp_type in
    let x = Names.fresh ctx.names "tmp" in
    let v = R.Expr.var ~loc:l (name ~loc:l x) in
    let init = R.Stmt.expr_rhs (R.Expr.call ~loc:l (name ~loc:l f) (atomic :: args)) in
    let* how = how default in
    let step = Option.map op ~f:(fun (op, field) -> (op, field, atomic, args, v)) in
    let* step =
      linearize ?step ~value:v ~access_type:e.exp_type ctx ~at how
        (R.Stmt.local ~loc:l ~typ ~init (ident ~loc:l x))
    in
    Ok (step, v)
  in
  let* elt =
    match args with
    | a :: _ when not (String.is_prefix op ~prefix:"make") -> element a.exp_type
    | _ -> element e.exp_type
  in
  let* field = atomic_field ctx ~at elt in
  let* nested = nested_stateful_read ctx.access_proofs e in
  let* stmts, values =
    match nested with
    | Some argument ->
        let* stmts, value = expr ~continue_state:true ctx argument in
        Ok (stmts, [ value ])
    | None -> operands ctx args
  in
  let primitive op = primitive ctx ~at elt op in
  match (op, values) with
  | ("make" | "make_contended"), [ v ] ->
      let x = Names.fresh ctx.names "tmp" in
      let views, view_args = view_allocation ctx ~loc:l [ field ] in
      let* explicit = allocation_initializers ctx e in
      let init =
        R.Stmt.new_rhs ((qualified_name ~loc:l field, Some v) :: (view_args @ explicit))
      in
      Ok
        ( stmts @ views
          @ R.Stmt.local ~loc:l ~typ:(R.Type.ref ~loc:l) ~init (ident ~loc:l x),
          R.Expr.var ~loc:l (name ~loc:l x) )
  | "get", [ a ] ->
      let* typ = typ ctx ~at e.exp_type in
      let x = Names.fresh ctx.names "tmp" in
      let read = R.Stmt.expr_rhs (R.Expr.field ~loc:l a (qualified_name ~loc:l field)) in
      let* how = how `Abort in
      let value = R.Expr.var ~loc:l (name ~loc:l x) in
      let* step =
        linearize ~value ~access_type:e.exp_type ctx ~at how
          (R.Stmt.local ~loc:l ~typ ~init:read (ident ~loc:l x))
      in
      record_read ctx ~atomic:a value;
      Ok (stmts @ step, R.Expr.var ~loc:l (name ~loc:l x))
  | "set", [ a; v ] ->
      let* how = how `Commit in
      let* step =
        linearize ~value:(unit_value ~loc:l) ~access_type:e.exp_type ctx ~at how
          [ write ~loc:l a field v ]
      in
      Ok (stmts @ step, unit_value ~loc:l)
  | "exchange", [ a; v ] ->
      let* f = primitive Exchange in
      let* reading, r = result f a [ v ] in
      Ok (stmts @ reading, r)
  | "compare_and_set", [ a; old_val; new_val ] ->
      let* f = primitive Compare_and_set in
      let* reading, r =
        result ~default:`Cas ~op:("compare_and_set", field) f a [ old_val; new_val ]
      in
      Ok (stmts @ reading, r)
  | "fetch_and_add", [ a; n ] ->
      let* f = primitive Fetch_and_add in
      let* reading, r = result f a [ n ] in
      Ok (stmts @ reading, r)
  | (("incr" | "decr") as op), [ a ] ->
      let* f = primitive Fetch_and_add in
      let x = Names.fresh ctx.names "tmp" in
      let n = R.Expr.int ~loc:l (if String.equal op "incr" then 1 else -1) in
      let init = R.Stmt.expr_rhs (R.Expr.call ~loc:l (name ~loc:l f) [ a; n ]) in
      let* how = how `Commit in
      let* step =
        linearize ~value:(unit_value ~loc:l) ~access_type:e.exp_type ctx ~at how
          (R.Stmt.local ~loc:l ~typ:(R.Type.int ~loc:l) ~init (ident ~loc:l x))
      in
      Ok (stmts @ step, unit_value ~loc:l)
  | _ -> unsupported at ("Atomic." ^ op)

(** The application of the operator or function at [path] to [args], in [e]. *)
and apply_operator ctx (e : Typedtree.expression) (path : Path.t)
    (args : Typedtree.expression list) =
  let at = e.exp_loc in
  let l = loc at in
  match (binop_of_path path, unop_of_path path, args) with
  | Some (Eq | Neq), _, [ a; b ] when runtime_structural_equality_unsafe ctx path a b ->
      error at "Structural equality on values containing references is unsupported"
  | Some ((And | Or) as op), _, [ a; b ] ->
      (* The right operand is evaluated only if the left one does not decide. *)
      let* a_stmts, a = expr ctx a in
      let before = ctx.snapshots and before_positions = ctx.positions in
      let* b_stmts, b = expr ctx b in
      (* The snapshots that the right operand takes are on one path only. *)
      ctx.snapshots <- common_snapshots [ before; ctx.snapshots ];
      ctx.positions <- before_positions;
      if List.is_empty b_stmts then Ok (a_stmts, R.Expr.binary ~loc:l op a b)
      else
        let then_, else_ =
          match op with And -> (`Rhs, `Value false) | _ -> (`Value true, `Rhs)
        in
        let* stmts, v =
          branch ctx e (fun target ->
              let target = Option.value_exn target in
              let arm = function
                | `Rhs -> b_stmts @ [ assign target b ]
                | `Value v -> [ assign target (R.Expr.bool ~loc:l v) ]
              in
              Ok [ R.Stmt.if_ ~loc:l a (arm then_) (arm else_) ])
        in
        Ok (a_stmts @ stmts, v)
  | Some ((Eq | Neq) as op), _, [ a; b ]
    when is_physical path && not (exact_physical ctx.types a b) ->
      let* b_stmts, b = expr ctx b in
      let* a_stmts, a = expr ctx a in
      let x = Names.fresh ctx.names "same" in
      let same = R.Expr.var ~loc:l (name ~loc:l x) in
      Ok
        ( b_stmts @ a_stmts
          @ R.Stmt.local ~loc:l ~typ:(R.Type.bool ~loc:l) (ident ~loc:l x)
          @ [
              R.Stmt.havoc ~loc:l (name ~loc:l x);
              R.Stmt.assume ~loc:l
                (R.Spec.make
                   (R.Expr.binary ~loc:l Impl same (R.Expr.binary ~loc:l Eq a b)));
            ],
          match op with Eq -> same | _ -> R.Expr.not_ ~loc:l same )
  | Some op, _, [ a; b ] ->
      let divisor = b.exp_loc in
      let* b_stmts, b = expr ctx b in
      let* a_stmts, a = expr ctx a in
      let stmts = b_stmts @ a_stmts in
      let nonzero () =
        check ctx ~at:divisor "This divisor may be zero"
          (R.Expr.binary ~loc:(loc divisor) Neq b (R.Expr.int ~loc:(loc divisor) 0))
      in
      let checked what v = Ok (stmts @ [ no_overflow ctx ~at what v ], v) in
      begin match op with
      | Plus -> checked "addition" (R.Expr.binary ~loc:l op a b)
      | Minus -> checked "subtraction" (R.Expr.binary ~loc:l op a b)
      | Mult -> checked "multiplication" (R.Expr.binary ~loc:l op a b)
      | Div ->
          let v = prelude_call ~loc:l Prelude.div [ a; b ] in
          let nonzero = nonzero () in
          Ok (stmts @ [ nonzero; no_overflow ctx ~at "division" v ], v)
      | Mod ->
          let nonzero = nonzero () in
          Ok (stmts @ [ nonzero ], prelude_call ~loc:l Prelude.mod_ [ a; b ])
      | _ -> Ok (stmts, R.Expr.binary ~loc:l op a b)
      end
  | _, Some op, [ a ] -> (
      let* stmts, a = expr ctx a in
      match op with
      | `Not -> Ok (stmts, R.Expr.not_ ~loc:l a)
      | `Neg ->
          let v = R.Expr.neg ~loc:l a in
          Ok (stmts @ [ no_overflow ctx ~at "negation" v ], v))
  | None, None, _ -> (
      let* path = Source.normalize_value_path e.exp_env ~at path in
      match resolved_call ctx.functions ctx.libraries path with
      | Some f -> call ctx e f args
      | None -> (
          match path with
          | Pident _ -> unsupported at "A call of a local function"
          | _ -> unsupported at ("A call of " ^ Path.name path)))
  | _ -> unsupported at "This application"

(** The call of the top-level function [f] with [args], in [e]: a statement, whose result
    is kept in a variable unless it is unit. *)
and call ctx (e : Typedtree.expression) f (ocaml_args : Typedtree.expression list) =
  let* arguments, args = operands ctx ocaml_args in
  let signature = List.Assoc.find ctx.procedure_signatures f ~equal:String.equal in
  let inputs = Option.value_map signature ~default:[] ~f:(fun s -> s.procedure_inputs) in
  let outputs =
    Option.value_map signature ~default:[] ~f:(fun s -> s.procedure_outputs)
  in
  let run explicit =
    call_prepared ctx e f ocaml_args args ~explicit ~signature_outputs:outputs
  in
  let annotation =
    List.Assoc.find ctx.access_proofs
      (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum)
      ~equal:Poly.equal
  in
  match annotation with
  | None ->
      let* statements, value, _ = run None in
      Ok (arguments @ statements, value)
  | Some annotation ->
      let result = ref None in
      let* statements =
        access_proof ctx annotation ~result_type:e.exp_type
          ~input_types:(List.map inputs ~f:snd) ~output_types:(List.map outputs ~f:snd)
          (fun values ->
            let* statements, value, outputs = run (Some values) in
            result := Some value;
            Ok (statements, value, outputs))
      in
      begin match !result with
      | Some value -> Ok (arguments @ statements, value)
      | None -> error annotation.loc "The scope did not invoke its attached call"
      end

and call_prepared ctx (e : Typedtree.expression) f ocaml_args args ~explicit
    ~signature_outputs =
  let l = loc e.exp_loc in
  let stmts = [] in
  (* A lifted local function takes the parameters of the function it continues first. *)
  let prefix, captured, role =
    Option.value (List.Assoc.find ctx.lifted f ~equal:String.equal) ~default:(0, [], None)
  in
  let* prefix =
    if List.length ctx.formals >= prefix then Ok (List.take ctx.formals prefix)
    else error e.exp_loc "This call needs the parameters of the function it continues"
  in
  let* captured =
    all captured ~f:(fun x ->
        match Names.find ctx.names x with
        | Some y -> Ok (R.Expr.var ~loc:l (name ~loc:l y))
        | None ->
            error e.exp_loc (Printf.sprintf "%s is not in scope here" (Ident.name x)))
  in
  let prefix = prefix @ captured in
  (* A ghost argument is the value of which the argument a precondition relates it to is a
     field, as [q] for [tail] in [fix_tail tail new_tail] after [push { tail; _ }]. *)
  let* ghosts =
    match explicit with
    | Some values -> Ok values
    | None ->
        all
          (Option.value
             (List.Assoc.find ctx.ghost_args f ~equal:String.equal)
             ~default:[])
          ~f:(fun equation ->
            let known =
              Option.bind equation ~f:(fun (i, field) ->
                  match List.nth ocaml_args (i - List.length prefix) with
                  | Some { exp_desc = Texp_ident (Pident id, _, _); _ } ->
                      Option.bind (Names.find ctx.names id) ~f:(fun x ->
                          List.find_map ctx.fields_of ~f:(fun (y, (g, value)) ->
                              Option.some_if
                                (String.equal x y && String.equal g field)
                                value))
                  | _ -> None)
            in
            match (known, equation) with
            | Some value, _ -> Ok value
            | None, None ->
                error e.exp_loc
                  "Caravan cannot tell the ghost argument of this call: give the callee \
                   a precondition that makes a parameter a field of it, as tail = q.tail"
            | None, Some (_, field) ->
                error e.exp_loc
                  (Printf.sprintf
                     "Caravan cannot tell the ghost argument of this call: the argument \
                      is not a variable known to be the field %s of a value, as one a \
                      record pattern binds"
                     field))
  in
  let args = prefix @ args @ ghosts in
  (* A recursive call before the function linearizes is a retry, which linearizes it in
     its place, with the atomic update's values of the implicit parameters, as does a call
     of a function that continues the update. *)
  let* retry =
    match ctx.au with
    | Some au
      when String.equal au.self f || Option.exists role ~f:(fun r -> Ident.same r au.role)
      ->
        begin match au.state with
        | Pending ->
            let* opening, values = au.open_ ~at:e.exp_loc ~unfold:false in
            au.values <- values;
            au.step <- e.exp_loc;
            au.state <- Committed;
            Ok (Some (au, opening, values))
        | Committed -> Ok None
        | Committing | On_cas | On_read _ | Partly | Registered _ | Unknown ->
            error e.exp_loc
              "Caravan cannot tell whether the function has linearized before this call"
        end
    | _ -> Ok None
  in
  let opening, implicit =
    Option.value_map retry ~default:([], []) ~f:(fun (_, o, values) -> (o, values))
  in
  (* The retry commits with its result. *)
  let closing value =
    Option.value_map retry ~default:(Ok []) ~f:(fun (au, _, _) ->
        au.close Commit_call ~value)
  in
  (* The latest snapshot witnesses the facts about earlier states that the callee
     requires, with the arguments' positions in it. *)
  let* witnesses =
    all
      (Option.value (List.Assoc.find ctx.pasts f ~equal:String.equal) ~default:[])
      ~f:(fun (inv, field, i) ->
        let structure =
          List.find ctx.shared.structures ~f:(fun st -> String.equal st.invariant inv)
        in
        match (structure, List.Assoc.find ctx.snapshots inv ~equal:String.equal) with
        | _ when Option.is_some (known_position ctx inv field (List.nth_exn args i)) ->
            let p =
              Option.value_exn (known_position ctx inv field (List.nth_exn args i))
            in
            Ok [ p.pos_snapshot; p.pos_k ]
        | Some st, Some (latest :: _) ->
            let index = List.Assoc.find_exn latest.indices field ~equal:String.equal in
            Ok
              [
                state_of ~loc:l st (grown st latest.values);
                R.Expr.index ~loc:l index (List.nth_exn args i);
              ]
        | _ ->
            error e.exp_loc
              "This call needs a fact about an earlier state, of which no snapshot was \
               taken")
  in
  (* A library's procedure is qualified by its module, as [Backoff.once]. *)
  let callee_name = qualified_name ~loc:l f in
  let callee = R.Expr.call ~loc:l callee_name (args @ List.concat witnesses @ implicit) in
  (* The ghost results witnessing facts about the state after the call: the caller's own,
     if the callee continues its update with the same ones. *)
  let ghost_facts =
    Option.value (List.Assoc.find ctx.past_returns f ~equal:String.equal) ~default:[]
  in
  let ghost_count = 2 * List.length ghost_facts in
  let ghost_decls, ghosts =
    match retry with
    | Some (au, _, _) when ghost_count > 0 && List.length au.ghost_results = ghost_count
      ->
        ([], au.ghost_results)
    | _ ->
        let fresh =
          List.concat_map ghost_facts ~f:(fun (inv, _, _) ->
              let st =
                List.find_exn ctx.shared.structures ~f:(fun st ->
                    String.equal st.invariant inv)
              in
              [
                ( Names.fresh ctx.names "snapshot",
                  R.Type.named ~loc:l
                    (generated_module_member ~loc:l (module_name st "state") "T")
                    [] );
                (Names.fresh ctx.names "position", R.Type.int ~loc:l);
              ])
        in
        ( List.concat_map fresh ~f:(fun (x, typ) ->
              R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x)),
          List.map fresh ~f:(fun (x, _) -> R.Expr.var ~loc:l (name ~loc:l x)) )
  in
  (* The ghost results witness the positions of the entries the callee ensures. *)
  let rec witnessed facts ghosts =
    match (facts, ghosts) with
    | (inv, field, entry) :: facts, snapshot :: k :: ghosts ->
        let rest = witnessed facts ghosts in
        begin match entry args with
        | Some e ->
            {
              pos_inv = inv;
              pos_field = field;
              pos_element = e;
              pos_snapshot = snapshot;
              pos_k = k;
            }
            :: rest
        | None -> rest
        end
    | _ -> []
  in
  ctx.positions <- witnessed ghost_facts ghosts @ ctx.positions;
  let* public =
    all signature_outputs ~f:(fun (_, ty) ->
        let raven = Names.fresh ctx.names "ghost_result" in
        let* raven_type = typ ctx ~at:e.exp_loc ty in
        Ok
          ( R.Expr.var ~loc:l (name ~loc:l raven),
            R.Stmt.local ~loc:l ~ghost:true ~typ:raven_type (ident ~loc:l raven) ))
  in
  let public_values = List.map public ~f:fst in
  let ghost_decls = List.concat_map public ~f:snd @ ghost_decls in
  let ghosts = public_values @ ghosts in
  if is_unit e.exp_type then
    let* closing = closing (unit_value ~loc:l) in
    let call =
      match ghosts with
      | [] -> [ R.Stmt.call ~loc:l callee ]
      | _ -> ghost_decls @ [ R.Stmt.assign ~loc:l ghosts (R.Stmt.expr_rhs callee) ]
    in
    Ok (stmts @ opening @ call @ closing, unit_value ~loc:l, public_values)
  else
    let* typ = typ ctx ~at:e.exp_loc e.exp_type in
    let x = Names.fresh ctx.names "tmp" in
    let v = R.Expr.var ~loc:l (name ~loc:l x) in
    let def =
      match ghosts with
      | [] -> R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs callee) (ident ~loc:l x)
      | _ ->
          R.Stmt.local ~loc:l ~typ (ident ~loc:l x)
          @ ghost_decls
          @ [ R.Stmt.assign ~loc:l (v :: ghosts) (R.Stmt.expr_rhs callee) ]
    in
    let* closing = closing v in
    Ok (stmts @ opening @ def @ closing, v, public_values)

(** The statements evaluating [args], right to left as OCaml does, and their values. *)
and operands ctx (args : Typedtree.expression list) =
  let* evaluated = all (List.rev args) ~f:(fun arg -> expr ctx arg) in
  Ok (List.concat_map evaluated ~f:fst, List.rev_map evaluated ~f:snd)

(** The accesses and condition for matching [p] against [v], and its bindings. *)
and pattern ?guard ctx (p : Typedtree.pattern) (v : R.Expr.t) =
  let at = p.pat_loc in
  let l = loc at in
  let conjoin conds =
    List.reduce (List.filter_opt conds) ~f:(fun a b -> R.Expr.binary ~loc:l And a b)
  in
  let components guard ps values =
    let* matched =
      all (List.zip_exn ps values) ~f:(fun (p, (access, v)) ->
          let* nested, cond, binds = pattern ?guard ctx p v in
          Ok (access @ nested, cond, binds))
    in
    Ok
      ( List.concat_map matched ~f:(fun (access, _, _) -> access),
        conjoin (List.map matched ~f:(fun (_, cond, _) -> cond)),
        List.concat_map matched ~f:(fun (_, _, binds) -> binds) )
  in
  match p.pat_desc with
  | Tpat_any -> Ok ([], None, [])
  | Tpat_var (id, _, _) -> Ok ([], None, [ (id, v, p.pat_type) ])
  | Tpat_alias (q, id, _, _, _) ->
      let* access, cond, binds = pattern ?guard ctx q v in
      Ok (access, cond, binds @ [ (id, v, p.pat_type) ])
  | Tpat_constant (Const_int n) ->
      Ok ([], Some (R.Expr.binary ~loc:l Eq v (R.Expr.int ~loc:l n)), [])
  | Tpat_tuple ps ->
      let values = List.mapi ps ~f:(fun i _ -> ([], R.Expr.tuple_get ~loc:l v i)) in
      components guard (List.map ps ~f:snd) values
  | Tpat_record (fields, _) ->
      let* parts =
        all fields ~f:(fun (_, label, p) ->
            let* field = field_of_label ctx ~at label in
            match field with
            | Some (field, false) ->
                Ok (p, ([], R.Expr.field ~loc:l v (qualified_name ~loc:l field)))
            | Some (field, true) ->
                let* access, value =
                  ordinary_read ?guard ctx ~at ~field ~elt:label.lbl_arg v
                in
                Ok (p, (access, value))
            | None -> unsupported at "This field")
      in
      components guard (List.map parts ~f:fst) (List.map parts ~f:snd)
  | Tpat_construct (_, { cstr_name = ("true" | "false") as b; _ }, [], _) ->
      Ok
        ( [],
          Some (R.Expr.binary ~loc:l Eq v (R.Expr.bool ~loc:l (String.equal b "true"))),
          [] )
  | Tpat_construct (_, { cstr_name = "()"; _ }, [], _) -> Ok ([], None, [])
  | Tpat_construct (_, cstr, ps, _) ->
      begin match Datatypes.find_cstr ctx.types cstr with
      | None -> unsupported at "This constructor"
      | Some (_, c) ->
          let is_c = R.Expr.is_ ~loc:l v (ident ~loc:l c.raven) in
          let fields =
            List.map c.fields ~f:(fun f ->
                ([], R.Expr.field ~loc:l v (qualified_name ~loc:l f)))
          in
          let* access, cond, binds =
            components (conjoin [ guard; Some is_c ]) ps fields
          in
          Ok (access, conjoin [ Some is_c; cond ], binds)
      end
  | Tpat_or (p1, p2, _) -> begin
      let* a1, c1, b1 = pattern ?guard ctx p1 v in
      let* a2, c2, b2 = pattern ?guard ctx p2 v in
      match (a1, a2, c1, c2, b1, b2) with
      | [], [], Some c1, Some c2, [], [] ->
          Ok ([], Some (R.Expr.binary ~loc:l Or c1 c2), [])
      | [], [], _, _, [], [] -> Ok ([], None, [])
      | _ :: _, _, _, _, _, _ | _, _ :: _, _, _, _, _ ->
          unsupported at "An or-pattern reading a mutable field"
      | _ -> unsupported at "An or-pattern binding variables"
    end
  | _ -> unsupported at "This pattern"

(** The cases of a match on the value [v], with the value of the matching one assigned to
    [target] if there is one; [total] if OCaml found them exhaustive. *)
and match_cases ?commits ~tail ctx ~at v
    (cases : (Typedtree.pattern * Typedtree.expression) list) ~total target =
  let l = loc at in
  let enclosing_names = ctx.names.scope in
  (* Each case starts in the state of the atomic update before the match. *)
  let start = au_snapshot ctx in
  let ends = ref [] in
  let snapshot_ends = ref [] in
  let start_positions = ctx.positions in
  let join = new_join () in
  let position_ends = ref [] in
  let commits =
    match commits with
    | Some commits -> commits
    | None -> List.map cases ~f:(fun _ -> None)
  in
  (* Whether each case linearizes the function, if the scrutinee is the value of a read
     that left the atomic update open, by the case's body. *)
  let case_commits = List.zip_exn (List.map cases ~f:snd) commits in
  (* The body of a case, after defining the variables of its pattern. *)
  let case_body ?(names = enclosing_names) binds (rhs : Typedtree.expression) =
    ctx.names.scope <- names;
    restore_au ctx start;
    let commits =
      Option.join
        (List.Assoc.find case_commits rhs ~equal:(fun a b ->
             Poly.equal a.exp_loc b.exp_loc))
    in
    let* entry = enter_arm ctx ~commits in
    let* defs =
      all binds ~f:(fun (id, value, t) ->
          let* typ = typ ctx ~at t in
          let x = Names.bind ~typ:t ctx.names id in
          Ok
            (R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs value) (ident ~loc:l x)
            @ assume_in_range ~loc:l t x))
    in
    let* stmts, value = expr ~tail ctx rhs in
    let* finish = finish_arm ctx ~tail value in
    let assignment =
      Option.value_map target ~default:[] ~f:(fun t -> [ assign t value ])
    in
    ends := au_state ctx :: !ends;
    snapshot_ends := ctx.snapshots :: !snapshot_ends;
    position_ends := ctx.positions :: !position_ends;
    let assigned = end_arm ctx join ~start:start_positions in
    Ok (entry @ List.concat defs @ stmts @ finish @ assignment @ assigned)
  in
  let not_exhaustive () =
    [ check ctx ~at "This match may not be exhaustive" (R.Expr.bool ~loc:l false) ]
  in
  let* stmts =
    match flat_cases ctx v cases with
    | Some flat ->
        let* raven_cases =
          all flat ~f:(fun (case, binds, in_range, rhs, names) ->
              let* body = case_body ~names binds rhs in
              Ok (case, in_range @ body))
        in
        let has_default =
          List.exists flat ~f:(fun (case, _, _, _, _) ->
              match case with R.Expr.Default -> true | Case _ -> false)
        in
        let default =
          if total || has_default then [] else [ (R.Expr.Default, not_exhaustive ()) ]
        in
        Ok [ R.Stmt.match_ ~loc:l v (raven_cases @ default) ]
    | None ->
        let rec chain = function
          | [] -> Ok (if total then [] else not_exhaustive ())
          | [ (p, rhs) ] when total ->
              let* access, _, binds = pattern ctx p v in
              let* body = case_body binds rhs in
              Ok (access @ body)
          | (p, rhs) :: rest -> begin
              let* access, cond, binds = pattern ctx p v in
              let* body = case_body binds rhs in
              match cond with
              | None -> Ok (access @ body)
              | Some cond ->
                  let* rest = chain rest in
                  Ok (access @ [ R.Stmt.if_ ~loc:l cond body rest ])
            end
        in
        chain cases
  in
  set_au_state ctx
    (Option.first_some
       (List.reduce (List.filter_opt !ends) ~f:join_au)
       (Option.map
          (let au, _, _ = start in
           au)
          ~f:(fun (state, _, _, _) -> state)));
  ctx.snapshots <- common_snapshots !snapshot_ends;
  ctx.positions <- join_positions join ~start:start_positions !position_ends;
  Ok (join.decls @ stmts)

(** The cases of a Raven match on [v] for [cases], if their patterns are flat: distinct
    constructors with variables or [_] as arguments, possibly followed by a variable or
    [_] matching anything else. *)
and flat_cases ctx v cases =
  let enclosing_names = ctx.names.scope in
  let flat_arg (p : Typedtree.pattern) =
    match p.pat_desc with
    | Tpat_any -> Some None
    | Tpat_var (id, _, _) -> Some (Some (id, p.pat_type))
    | _ -> None
  in
  let rec flat seen = function
    | [] -> Some []
    | [ ((p : Typedtree.pattern), rhs) ] when Option.is_some (flat_arg p) ->
        Some [ (`Any (Option.map (Option.join (flat_arg p)) ~f:fst, p), rhs) ]
    | ((p : Typedtree.pattern), rhs) :: rest ->
        begin match p.pat_desc with
        | Tpat_construct (_, cstr, ps, _) ->
            begin match
              (Datatypes.find_cstr ctx.types cstr, Option.all (List.map ps ~f:flat_arg))
            with
            | Some (_, c), Some args when not (List.mem seen c.raven ~equal:String.equal)
              ->
                Option.map
                  (flat (c.raven :: seen) rest)
                  ~f:(fun rest -> (`Ctor (c, args, p), rhs) :: rest)
            | _ -> None
            end
        | _ -> None
        end
  in
  let case item =
    ctx.names.scope <- enclosing_names;
    match item with
    | `Any (id, (p : Typedtree.pattern)), rhs ->
        let binds =
          Option.value_map id ~default:[] ~f:(fun id -> [ (id, v, p.pat_type) ])
        in
        (R.Expr.Default, binds, [], rhs, ctx.names.scope)
    | `Ctor ((c : Datatypes.ctor), args, (p : Typedtree.pattern)), rhs ->
        let l = loc p.pat_loc in
        let var = function
          | None -> (ident ~loc:l "_", [])
          | Some (id, t) ->
              let x = Names.bind ~typ:t ctx.names id in
              (ident ~loc:l x, assume_in_range ~loc:l t x)
        in
        let vars = List.map args ~f:var in
        ( R.Expr.Case (ident ~loc:l c.raven, List.map vars ~f:fst),
          [],
          List.concat_map vars ~f:snd,
          rhs,
          ctx.names.scope )
  in
  let result = Option.map (flat [] cases) ~f:(List.map ~f:case) in
  ctx.names.scope <- enclosing_names;
  result

(** [if c then e1 else e2], with its value assigned to [target] if there is one. *)
and conditional ctx ~at ?polarity ~tail c (e1 : Typedtree.expression)
    (e2 : Typedtree.expression option) target =
  let l = loc at in
  (* Each arm starts in the state of the atomic update before the branch; if [c] is the
     result of the [compare_and_set] that left the update open, the arms close it. *)
  let start = au_snapshot ctx in
  let start_positions = ctx.positions in
  let join = new_join () in
  let arm taken e =
    restore_au ctx start;
    let* entry =
      enter_arm ctx ~commits:(Option.map polarity ~f:(fun p -> Bool.equal p taken))
    in
    let* stmts =
      match e with
      | None -> finish_arm ctx ~tail (unit_value ~loc:l)
      | Some e ->
          let* stmts, v = expr ~tail ctx e in
          let* finish = finish_arm ctx ~tail v in
          let assignment =
            Option.value_map target ~default:[] ~f:(fun t -> [ assign t v ])
          in
          Ok (stmts @ finish @ assignment)
    in
    let assigned = end_arm ctx join ~start:start_positions in
    Ok (entry @ stmts @ assigned, (au_state ctx, ctx.snapshots, ctx.positions))
  in
  let* then_, (then_state, then_snapshots, then_positions) = arm true (Some e1) in
  let* else_, (else_state, else_snapshots, else_positions) = arm false e2 in
  set_au_state ctx (Option.map2 then_state else_state ~f:join_au);
  ctx.snapshots <- common_snapshots [ then_snapshots; else_snapshots ];
  ctx.positions <-
    join_positions join ~start:start_positions [ then_positions; else_positions ];
  Ok (join.decls @ [ R.Stmt.if_ ~loc:l c then_ else_ ])

(** The statements [make target] computing the value of [e] into a new variable [target],
    and that variable; no variable if [e] is of type unit. *)
and branch ctx (e : Typedtree.expression) make =
  let l = loc e.exp_loc in
  if is_unit e.exp_type then
    let* stmts = make None in
    Ok (stmts, unit_value ~loc:l)
  else
    let* typ = typ ctx ~at:e.exp_loc e.exp_type in
    let x = Names.fresh ctx.names "tmp" in
    let* stmts = make (Some (x, l)) in
    Ok
      ( R.Stmt.local ~loc:l ~const:false ~typ (ident ~loc:l x) @ stmts,
        R.Expr.var ~loc:l (name ~loc:l x) )

and assign (x, l) v =
  R.Stmt.assign ~loc:l [ R.Expr.var ~loc:l (name ~loc:l x) ] (R.Stmt.expr_rhs v)

(** The pure expression [e] as a Raven expression, with the values of its let-bound
    variables in [values]; [funcs] are the functions it may call, by their OCaml compiler
    paths, with their Raven names. *)
and pure ?(reads = []) ctx ~funcs (values : (string * R.Expr.t) list)
    (e : Typedtree.expression) : (R.Expr.t, error) Result.t =
  let at = e.exp_loc in
  let l = loc at in
  let pure_in values = pure ~reads ctx ~funcs values in
  let not_pure what =
    unsupported at (what ^ " in a function that contracts use, which must be pure,")
  in
  match e.exp_desc with
  | Texp_ident (Pident id, _, _) ->
      begin match
        ( List.Assoc.find values (Ident.unique_name id) ~equal:String.equal,
          Names.find ctx.names id )
      with
      | Some v, _ -> Ok v
      | None, Some x -> Ok (R.Expr.var ~loc:l (name ~loc:l x))
      | None, None -> not_pure "A function used as a value"
      end
  | Texp_ident (p, _, _) ->
      begin match stdlib_name p with
      | Some "max_int" -> Ok (R.Expr.int ~loc:l Prelude.max_int)
      | Some "min_int" -> Ok (R.Expr.int ~loc:l Prelude.min_int)
      | _ -> not_pure "This identifier"
      end
  | Texp_constant (Const_int n) -> Ok (R.Expr.int ~loc:l n)
  | Texp_construct ({ txt = Lident (("true" | "false") as b); _ }, _, []) ->
      Ok (R.Expr.bool ~loc:l (String.equal b "true"))
  | Texp_construct ({ txt = Lident "()"; _ }, _, []) -> Ok (unit_value ~loc:l)
  | Texp_construct (_, cstr, args) ->
      begin match Datatypes.find_cstr ctx.types cstr with
      | None -> not_pure "This constructor"
      | Some (d, c) ->
          let* args = all args ~f:(pure_in values) in
          Ok (R.Expr.call ~loc:l (Datatypes.ctor_name ~loc:l d c) args)
      end
  | Texp_tuple components ->
      let* components = all components ~f:(fun (_, c) -> pure_in values c) in
      Ok (R.Expr.tuple ~loc:l components)
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, _); _ },
        [ (Nolabel, Arg ({ exp_desc = Texp_ident (Pident r, _, _); _ } as cell)) ] )
    when Option.equal String.equal (stdlib_name path) (Some "!") ->
      begin match (Names.find ctx.names r, Datatypes.desc ctx.types cell.exp_type) with
      | Some x, Tconstr (_, [ elt ], _) -> begin
          let* field = ref_field ctx ~at elt in
          match List.Assoc.find reads (x, field) ~equal:Poly.equal with
          | Some v -> Ok v
          | None -> not_pure "A read of a reference"
        end
      | _ -> not_pure "A read of a reference"
      end
  | Texp_field ({ exp_desc = Texp_ident (Pident r, _, _); _ }, _, label)
    when Option.is_some (Names.find ctx.names r) -> begin
      let* field = field_of_label ctx ~at label in
      let x = Option.value_exn (Names.find ctx.names r) in
      match field with
      | Some (field, true) ->
          begin match List.Assoc.find reads (x, field) ~equal:Poly.equal with
          | Some v -> Ok v
          | None -> not_pure "A read of a reference"
          end
      | Some (field, false) ->
          Ok
            (R.Expr.field ~loc:l
               (R.Expr.var ~loc:l (name ~loc:l x))
               (qualified_name ~loc:l field))
      | None -> not_pure "This field"
    end
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, [ (_, Arg a); (_, Arg b) ])
    when runtime_structural_equality_unsafe ctx path a b ->
      error at "Structural equality on values containing references is unsupported"
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, [ (_, Arg a); (_, Arg b) ])
    when is_physical path && not (exact_physical ctx.types a b) ->
      not_pure "Physical equality on values that are not immediate"
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, args) -> begin
      let* args = plain_args ~at args in
      let* args = all args ~f:(pure_in values) in
      match (binop_of_path path, unop_of_path path, path, args) with
      | Some Div, _, _, [ a; b ] -> Ok (prelude_call ~loc:l Prelude.div [ a; b ])
      | Some Mod, _, _, [ a; b ] -> Ok (prelude_call ~loc:l Prelude.mod_ [ a; b ])
      | Some op, _, _, [ a; b ] -> Ok (R.Expr.binary ~loc:l op a b)
      | _, Some `Not, _, [ a ] -> Ok (R.Expr.not_ ~loc:l a)
      | _, Some `Neg, _, [ a ] -> Ok (R.Expr.neg ~loc:l a)
      | None, None, path, _ ->
          let* path = Source.normalize_value_path e.exp_env ~at path in
          begin match Path_bindings.find funcs path with
          | Some f -> Ok (R.Expr.call ~loc:l (qualified_name ~loc:l f) args)
          | None -> not_pure ("A call of " ^ Path.name path)
          end
      | _ -> not_pure "This application"
    end
  | Texp_ifthenelse (c, a, Some b) ->
      let* c = pure_in values c in
      let* a = pure_in values a in
      let* b = pure_in values b in
      Ok (R.Expr.ite ~loc:l c a b)
  | Texp_let
      ( Nonrecursive,
        [ { vb_pat = { pat_desc = Tpat_var (id, _, _); _ }; vb_expr; _ } ],
        body ) ->
      let* v = pure_in values vb_expr in
      pure_in ((Ident.unique_name id, v) :: values) body
  | Texp_match (scrutinee, cases, [], Total) -> begin
      let* v = pure_in values scrutinee in
      let* cases =
        all cases ~f:(fun (c : Typedtree.computation Typedtree.case) ->
            match (Typedtree.split_pattern c.c_lhs, c.c_guard) with
            | (Some p, None), None -> Ok (p, c.c_rhs)
            | _ -> not_pure "A guard or an exception case")
      in
      let with_binds binds =
        List.fold binds ~init:values ~f:(fun values (id, value, _) ->
            (Ident.unique_name id, value) :: values)
      in
      match flat_cases ctx v cases with
      | Some flat ->
          let* cases =
            all flat ~f:(fun (case, binds, _, rhs, _) ->
                let* body = pure_in (with_binds binds) rhs in
                Ok (case, body))
          in
          Ok (R.Expr.match_ ~loc:l v cases)
      | None ->
          (* OCaml found the cases exhaustive, so the last one needs no test. *)
          let rec chain = function
            | [] -> not_pure "An empty match"
            | [ (p, rhs) ] ->
                let* access, _, binds = pattern ctx p v in
                if List.is_empty access then pure_in (with_binds binds) rhs
                else not_pure "A pattern reading a mutable field"
            | (p, rhs) :: rest -> begin
                let* access, cond, binds = pattern ctx p v in
                if not (List.is_empty access) then
                  not_pure "A pattern reading a mutable field"
                else
                  let* body = pure_in (with_binds binds) rhs in
                  match cond with
                  | None -> Ok body
                  | Some cond ->
                      let* rest = chain rest in
                      Ok (R.Expr.ite ~loc:l cond body rest)
              end
          in
          chain cases
    end
  | Texp_match (_, _, _, Partial) -> not_pure "A match that may not be exhaustive"
  | _ -> not_pure "This expression"

type func = {
  id : Ident.t;
  namespace : string list;
  paths : Path.t list;
  environment : Env.t;
  signature_sites : Module_inventory.signature_value list;
  raven_name : string;
  params : Typedtree.function_param list;
  body : Typedtree.expression;
  loc : Location.t;
  contract : S.contract option;
  next : Location.t option;  (** The next item or the end of the enclosing scope. *)
  prefix : Ident.t list;
      (** The variables of the parameters of the function that a lifted local function
          continues, which its parameters start with. *)
  prefix_count : int;  (** The number of those parameters. *)
  captured : Ident.t list;
      (** The variables of its context that a lifted local function uses, which it takes
          next. *)
  manual : bool;
  trusted : bool;
      (** Whether the function is trusted, as [(*@ trusted *)] after it says: its contract
          assumed, its body not translated. *)
  role : Ident.t option;  (** The function whose atomic update it continues. *)
}
(** A top-level function [f] with its parameters [params] and [body], and its contract, or
    a local function lifted to the top level. *)

type runtime_plan = {
  body_types : Datatypes.t list;
  predicate_overrides : (string * (string * Types.type_expr list)) list;
  calls : string Path_bindings.t;
  pure_calls : string Path_bindings.t;
  representatives : func list;
  logical_calls : Qualified_name.t Path_bindings.t;
}

let contract_bound_names (f : func) =
  let found = ref [] in
  let pat : type k. Tast_iterator.iterator -> k Typedtree.general_pattern -> unit =
   fun iterator pattern ->
    (match pattern.pat_desc with
    | Tpat_var (id, _, _) | Tpat_alias (_, id, _, _, _) ->
        found := Ident.name id :: !found
    | _ -> ());
    Tast_iterator.default_iterator.pat iterator pattern
  in
  let iterator = { Tast_iterator.default_iterator with pat } in
  List.iter f.params ~f:(fun parameter ->
      match parameter.Typedtree.fp_kind with
      | Tparam_pat p | Tparam_optional_default (p, _) -> iterator.pat iterator p);
  let header = Option.bind f.contract ~f:(fun c -> c.S.header) in
  !found
  @ Option.value_map header ~default:[] ~f:(fun h ->
      List.filter_map (h.hd_args @ h.hd_ret) ~f:(function
        | S.Lvar id | Lghost (id, _) -> Some id.pid_str
        | Lunit _ | Lwild -> None))

let refers_to f term =
  List.exists
    (term_references (contract_bound_names f) term)
    ~f:(fun q ->
      Option.exists (Source.value_path f.environment q) ~f:(fun path ->
          List.mem f.paths path ~equal:Path.same))

(** The ghost parameters that the contract of [f] gives it, as [q] in
    [fix_tail [q : t] tail new_tail]. *)
let ghost_params (f : func) =
  match Option.bind f.contract ~f:(fun c -> c.header) with
  | Some h ->
      List.filter_map h.hd_args ~f:(function
        | S.Lghost (id, t) -> Some (id, t)
        | _ -> None)
  | None -> []

(** The ghost results declared after the concrete result of [f]. *)
let ghost_results (f : func) =
  match Option.bind f.contract ~f:(fun c -> c.header) with
  | Some h ->
      List.filter_map h.hd_ret ~f:(function
        | S.Lghost (id, t) -> Some (id, t)
        | _ -> None)
  | None -> []

(** The names that the contract of [f] gives its result and its [n] parameters, by its
    [header] if it has one, and otherwise OCaml's. *)
let contract_names (f : func) (header : S.header option) n =
  let ocaml_names =
    List.map f.params ~f:(fun p ->
        match p.fp_kind with
        | Tparam_pat { pat_desc = Tpat_var (id, _, _); _ } -> Some (Ident.name id)
        | _ -> None)
  in
  match header with
  | None -> Ok ("result", ocaml_names)
  | Some h ->
      let concrete_results =
        List.filter h.hd_ret ~f:(function S.Lghost _ -> false | _ -> true)
      in
      let* result =
        match concrete_results with
        | [ Lwild ] | [] -> Ok "result"
        | [ Lvar id ] -> Ok id.pid_str
        | _ -> unsupported h.hd_name.pid_loc "A contract naming several results"
      in
      let arg = function
        | S.Lvar id -> Ok (Some id.pid_str)
        | Lunit _ | Lwild | Lghost _ -> Ok None
      in
      (* Ghost parameters are not the function's. *)
      let h =
        {
          h with
          hd_args = List.filter h.hd_args ~f:(function S.Lghost _ -> false | _ -> true);
        }
      in
      if not (String.equal h.hd_name.pid_str (Ident.name f.id)) then
        error h.hd_name.pid_loc
          (Printf.sprintf "This contract is for %s, not %s" h.hd_name.pid_str
             (Ident.name f.id))
      else if List.length h.hd_args <> n then
        error h.hd_name.pid_loc
          (Printf.sprintf "This contract names %d arguments, but %s has %d"
             (List.length h.hd_args) (Ident.name f.id) n)
      else
        let* args = all h.hd_args ~f:arg in
        Ok (result, args)

(** The parameters of [f]: their OCaml and Raven names, unless unit, their range, and
    their declarations. A parameter that is a pattern, as [{ tail; _ }], is named as
    [names], those of the contract, name it, and binds its variables at the start of the
    body, by [pattern_params]. *)
let formals ?(names = []) ctx (f : func) =
  all
    (List.mapi f.params ~f:(fun i p -> (i, p)))
    ~f:(fun (i, (p : Typedtree.function_param)) ->
      match p.fp_kind with
      | Tparam_pat { pat_desc = Tpat_var (id, _, _); pat_type; pat_loc; _ }
        when Poly.equal p.fp_arg_label Asttypes.Nolabel ->
          let* typ = typ ctx ~at:pat_loc pat_type in
          let x = Names.bind ~typ:pat_type ctx.names id in
          Ok
            ( Some (Ident.name id, x),
              range_spec ~loc:(loc pat_loc) pat_type x,
              R.Var.make ~loc:(loc pat_loc) (ident ~loc:(loc pat_loc) x) typ )
      | Tparam_pat
          { pat_desc = Tpat_construct (_, { cstr_name = "()"; _ }, [], _); pat_loc; _ } ->
          let x = Names.fresh ctx.names "unit" in
          let l = loc pat_loc in
          Ok (None, None, R.Var.make ~loc:l (ident ~loc:l x) (R.Type.tuple ~loc:l []))
      | Tparam_pat { pat_desc = Tpat_record _ | Tpat_tuple _; pat_type; pat_loc; _ }
        when Poly.equal p.fp_arg_label Asttypes.Nolabel ->
          let* typ = typ ctx ~at:pat_loc pat_type in
          let contract_name = Option.join (List.nth names i) in
          let x = Names.fresh ctx.names (Option.value contract_name ~default:"arg") in
          let l = loc pat_loc in
          Ok
            ( Some (Option.value contract_name ~default:"", x),
              None,
              R.Var.make ~loc:l (ident ~loc:l x) typ )
      | _ -> unsupported p.fp_loc "This parameter")

(** The statements binding the variables of the parameters of [f] that are patterns to the
    parts of their values, [formals]. *)
let pattern_params ctx (f : func) formals =
  let* bindings =
    all (List.zip_exn f.params formals)
      ~f:(fun ((p : Typedtree.function_param), (ocaml, _, _)) ->
        match (p.fp_kind, ocaml) with
        | ( Tparam_pat ({ pat_desc = Tpat_record _ | Tpat_tuple _; pat_loc; _ } as pat),
            Some (_, x) ) ->
            let l = loc pat_loc in
            let value = R.Expr.var ~loc:l (name ~loc:l x) in
            let* access, cond, binds = pattern ctx pat value in
            begin match cond with
            | Some _ -> unsupported pat_loc "A refutable pattern as a parameter"
            | None ->
                let* stmts =
                  all binds ~f:(fun (id, value, t) ->
                      let* typ = typ ctx ~at:pat_loc t in
                      let y = Names.bind ~typ:t ctx.names id in
                      Ok
                        (R.Stmt.local ~loc:l ~const:true ~typ
                           ~init:(R.Stmt.expr_rhs value) (ident ~loc:l y)
                        @ assume_in_range ~loc:l t y))
                in
                (* The variables of a record's fields are its fields. *)
                begin match pat.pat_desc with
                | Tpat_record (fields, _) ->
                    List.iter fields ~f:(fun (_, label, p) ->
                        match p.pat_desc with
                        | Tpat_var (id, _, _) ->
                            Option.iter (Names.find ctx.names id) ~f:(fun y ->
                                ctx.fields_of <-
                                  (y, (label.lbl_name, value)) :: ctx.fields_of)
                        | _ -> ())
                | _ -> ()
                end;
                Ok (access :: stmts)
            end
        | _ -> Ok [])
  in
  Ok (List.concat (List.concat bindings))

(** The names that the contract of [f] uses for its result and parameters, with the Raven
    names of the result, [result], and of the parameters, [formals]. *)
let rec contract_env ctx ~spec_funcs (f : func) formals ~result =
  let header = Option.bind f.contract ~f:(fun c -> c.header) in
  let* result_name, arg_names = contract_names f header (List.length formals) in
  let param_types =
    List.map f.params ~f:(fun p ->
        match p.fp_kind with Tparam_pat pat -> Some pat.pat_type | _ -> None)
  in
  let params =
    List.map2_exn (List.zip_exn arg_names param_types) formals
      ~f:(fun (contract_name, t) (ocaml, _, _) ->
        let raven = Option.value_map ocaml ~default:"" ~f:snd in
        Option.map contract_name ~f:(fun n -> (n, raven, t)))
    |> List.filter_map ~f:Fn.id
  in
  let named = (result_name, result, Some f.body.exp_type) :: params in
  let types =
    List.filter_map named ~f:(fun (x, _, t) -> Option.map t ~f:(fun t -> (x, t)))
  in
  let env =
    {
      ctx;
      var_types = types;
      logical_definition = false;
      data = ctx.types;
      funcs = spec_funcs;
      vars =
        ( result_name,
          if is_unit f.body.exp_type then Value (unit_value ~loc:(loc f.loc))
          else Raven result )
        :: List.map params ~f:(fun (x, r, _) -> (x, Raven r));
    }
  in
  (* Ghost parameters, as [q] in [fix_tail [q : t] tail new_tail]. *)
  let declared_inputs = ghost_params f in
  let* ghosts =
    all
      (List.mapi declared_inputs ~f:(fun i input -> (i, input)))
      ~f:(fun (i, (id, pty)) ->
        let* () =
          if
            List.Assoc.mem env.vars id.pid_str ~equal:String.equal
            || List.exists (List.take declared_inputs i) ~f:(fun (earlier, _) ->
                String.equal earlier.pid_str id.pid_str)
          then
            error id.pid_loc
              (Printf.sprintf "The ghost parameter %s repeats another contract name"
                 id.pid_str)
          else Ok ()
        in
        let* t = Source.ocaml_type ctx.env ~at:id.pid_loc pty in
        Ok (id.pid_str, Names.fresh ctx.names id.pid_str, t))
  in
  let env =
    List.fold ghosts ~init:env ~f:(fun env (x, raven, t) ->
        { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
  in
  let declared_outputs = ghost_results f in
  let* output_ghosts =
    all
      (List.mapi declared_outputs ~f:(fun i output -> (i, output)))
      ~f:(fun (i, (id, pty)) ->
        let* () =
          if
            List.Assoc.mem env.vars id.pid_str ~equal:String.equal
            || List.exists (List.take declared_outputs i) ~f:(fun (earlier, _) ->
                String.equal earlier.pid_str id.pid_str)
          then
            error id.pid_loc
              (Printf.sprintf "The ghost result %s repeats another contract name"
                 id.pid_str)
          else Ok ()
        in
        let* t = Source.ocaml_type ctx.env ~at:id.pid_loc pty in
        Ok (id.pid_str, Names.fresh ctx.names id.pid_str, t))
  in
  let* () =
    let preconditions =
      Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires @ c.atomic_requires)
    in
    Result.all_unit
      (List.map preconditions ~f:(fun t ->
           match
             List.find output_ghosts ~f:(fun (x, _, _) ->
                 List.mem (term_names t) x ~equal:String.equal)
           with
           | Some (x, _, _) ->
               error t.term_loc
                 (Printf.sprintf "The ghost result %s is unavailable in a precondition" x)
           | None -> Ok ()))
  in
  let env =
    List.fold output_ghosts ~init:env ~f:(fun env (x, raven, t) ->
        { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
  in
  let env = pattern_definitions env f in
  let* implicit = implicit_vars env f in
  let env =
    List.fold implicit ~init:env ~f:(fun env (x, raven, t, _) ->
        { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
  in
  Ok (result_name, env, implicit, ghosts)

(** [env] with the names that preconditions of [f] define by a constructor's arguments, as
    [c] in [requires node === Next (v, c)]: the value's fields. *)
and pattern_definitions env (f : func) =
  let l = R.Loc.none in
  let requires = Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires) in
  let rec conjuncts (t : S.term) =
    match spine (S.chain t) [] with
    | { term_desc = Tvar (Qid { pid_str = "&&" | "/\\"; _ }); _ }, [ a; b ] ->
        conjuncts a @ conjuncts b
    | _ -> [ S.chain t ]
  in
  let define env (t : S.term) =
    match spine t [] with
    | ( { term_desc = Tvar (Qid { pid_str = "=" | "==" | "==="; _ }); _ },
        [ ({ term_desc = Tvar (Qid { pid_str = x; _ }); _ } as value); rhs ] )
      when List.Assoc.mem env.vars x ~equal:String.equal ->
        begin match spine rhs [] with
        | { term_desc = Tvar (Qid { pid_str = c; _ } as q); _ }, args
          when Char.is_uppercase c.[0] -> begin
            let args =
              match args with [ { term_desc = Ttuple ts; _ } ] -> ts | _ -> args
            in
            match (find_constructor env q, formula env value) with
            | Some (_, ctor), Ok v when List.length ctor.fields = List.length args ->
                List.fold
                  (List.zip_exn args (List.zip_exn ctor.fields ctor.args))
                  ~init:env
                  ~f:(fun env ((a : S.term), (field, typ)) ->
                    match a.term_desc with
                    | Tvar (Qid { pid_str = y; _ })
                      when Char.is_lowercase y.[0]
                           && not (List.Assoc.mem env.vars y ~equal:String.equal) ->
                        {
                          (bind env y
                             (Value (R.Expr.field ~loc:l v (qualified_name ~loc:l field))))
                          with
                          var_types = (y, typ) :: env.var_types;
                        }
                    | _ -> env)
            | _ -> env
          end
        | _ -> env
        end
    | _ -> env
  in
  List.fold (List.concat_map requires ~f:conjuncts) ~init:env ~f:define

(** The names free in the preconditions of [f] that [env] does not bind: implicit ghost
    parameters, as [n] in [requires own c.count n], with their Raven names, OCaml types
    and declarations. A name owned as the value of a field has that field's type. *)
and implicit_vars env (f : func) =
  let requires =
    Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires @ c.atomic_requires)
  in
  let* free = free_typed env requires ~at:f.loc in
  Ok
    (List.map free ~f:(fun (x, raven, t, typ, l) ->
         ( x,
           raven,
           t,
           R.Var.make ~loc:l ~ghost:true ~implicit:true (ident ~loc:l raven) typ )))

(** Translates each contract channel, quantifying its postcondition-only names. *)
let contract_postconditions env ~at ?atomic posts =
  let l = loc at in
  let* free = free_typed env posts ~at in
  match (free, posts) with
  | [], _ | _, [] ->
      all posts ~f:(fun t ->
          Result.map (formula env t) ~f:(fun e -> R.Spec.make ?atomic e))
  | _ ->
      let env =
        List.fold free ~init:env ~f:(fun env (x, raven, t, _, _) ->
            { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
      in
      let* posts = all posts ~f:(formula env) in
      let conj = List.reduce_exn posts ~f:(fun a b -> R.Expr.binary ~loc:l And a b) in
      let vars =
        List.map free ~f:(fun (_, raven, _, typ, var_loc) ->
            R.Var.make ~loc:var_loc (ident ~loc:var_loc raven) typ)
      in
      Ok [ R.Spec.make ?atomic (R.Expr.exists ~loc:l vars conj) ]

(** The function that contracts call for [f], defined by its body; [funcs] are the
    functions it may call, by their compiler paths, and [spec_funcs] by their OCaml names.
    Its postconditions are those of [f], under the preconditions that do not call [f]
    itself: these are proven for the function's value, by induction, which a precondition
    bounding the function's own value, as for the code to not overflow, would make
    circular. *)
let func types ~refs ~primitives ~shared ~ocaml_env ~preds ~funcs ~spec_funcs
    ~proof_support ?declaration_name ?(primitive_namespace = []) origins (f : func) :
    (R.Callable.t, error) Result.t =
  let ctx =
    {
      types;
      refs;
      primitives;
      primitive_namespace;
      names = Names.create ();
      functions = Path_bindings.empty;
      lifted = [];
      pasts = [];
      past_returns = [];
      origins;
      annotations = [];
      spec_funcs;
      proof_lemmas = [];
      proof_support;
      predicate_bodies = [];
      env = ocaml_env;
      preds;
      facts = [];
      au = None;
      current_procedure = None;
      manual = false;
      access_proofs = [];
      return_proofs = [];
      procedure_signatures = [];
      ghost_returns = [];
      proof_state = None;
      return_covered = false;
      initializations = [];
      linearizations = [];
      shared;
      invariants = [];
      opened = [];
      snapshots = [];
      positions = [];
      formals = [];
      ghost_args = [];
      fields_of = [];
      libraries = Path_bindings.empty;
    }
  in
  let l = loc f.loc in
  let* () =
    if f.trusted then unsupported f.loc "A trusted function that contracts call"
    else Ok ()
  in
  let* formals = formals ctx f in
  let result = Names.fresh ctx.names "result" in
  let* _, env, implicit, ghosts = contract_env ctx ~spec_funcs f formals ~result in
  let* () =
    match ghosts with
    | [] -> Ok ()
    | _ -> unsupported f.loc "A pure function with ghost parameters"
  in
  let* () =
    match implicit with
    | [] -> Ok ()
    | _ -> unsupported f.loc "A pure function with ghost parameters"
  in
  let calls_self = refers_to f in
  let clauses select = Option.value_map f.contract ~default:[] ~f:select in
  let* requires =
    all
      (List.filter (clauses (fun c -> c.requires)) ~f:(fun t -> not (calls_self t)))
      ~f:(formula env)
  in
  let* ensures = all (clauses (fun c -> c.ensures)) ~f:(formula env) in
  let ensures =
    List.map ensures ~f:(fun post ->
        R.Spec.make
          (List.fold_right requires ~init:post ~f:(fun pre post ->
               R.Expr.binary ~loc:l Impl pre post)))
  in
  let* result_typ = typ ctx ~at:f.body.exp_loc f.body.exp_type in
  let* body = pure ctx ~funcs [] f.body in
  Ok
    (R.Callable.func ~loc:l
       ~formals:(List.map formals ~f:(fun (_, _, v) -> v))
       ~returns:[ R.Var.make ~loc:l (ident ~loc:l result) result_typ ]
       ~ensures
       (ident ~loc:l (Option.value declaration_name ~default:f.raven_name))
       (Some body))

(** The statements folding, or unfolding with [make], the predicates that the formula [t]
    applies, following its conditionals and matches, as
    [match xs with [] -> stack t [] | _ :: xs' -> stack t xs']. *)
let rec uses ctx env ~(at : Location.t) make (t : S.term) =
  let l = loc at in
  let t = S.chain t in
  let head, args = spine t [] in
  match (head.term_desc, args, t.term_desc) with
  | Tvar (Qid { pid_str = "&&" | "/\\"; _ }), [ a; b ], _ ->
      let* a = uses ctx env ~at make a in
      let* b = uses ctx env ~at make b in
      Ok (a @ b)
  | Tvar q, _, _
    when List.mem ctx.proof_support.opaque_predicates (logical_key env q)
           ~equal:String.equal ->
      Ok []
  | Tvar q, _, _ when List.Assoc.mem ctx.preds (logical_key env q) ~equal:String.equal ->
      let key = logical_key env q in
      let raven, types = List.Assoc.find_exn ctx.preds key ~equal:String.equal in
      let* args =
        predicate_arguments env ~at:t.term_loc ~display:(qualid_key q) key types args
      in
      Ok (make ~loc:l ~pred:key (qualified_name ~loc:l raven) args)
  | _, _, Tif (c, a, b) ->
      let* c = formula env c in
      let* a = uses ctx env ~at make a in
      let* b = uses ctx env ~at make b in
      Ok
        (if List.is_empty a && List.is_empty b then []
         else [ R.Stmt.ghost_block ~loc:l [ R.Stmt.if_ ~loc:l c a b ] ])
  | _, _, Tmatch (scrutinee, cases) ->
      let* v = formula env scrutinee in
      let rec chain = function
        | [] -> Ok []
        | (p, body) :: rest -> begin
            let* cond, binds = spec_pattern env p v in
            let env =
              List.fold binds ~init:env ~f:(fun env (x, v) -> bind env x (Value v))
            in
            let* body = uses ctx env ~at make body in
            match (cond, rest) with
            | None, _ | _, [] -> Ok body
            | Some cond, _ ->
                let* rest = chain rest in
                Ok
                  (if List.is_empty body && List.is_empty rest then []
                   else [ R.Stmt.ghost_block ~loc:l [ R.Stmt.if_ ~loc:l cond body rest ] ])
          end
      in
      chain cases
  | _, _, (Tattr (_, t) | Tcast (t, _)) -> uses ctx env ~at make t
  | _ -> Ok []

(** The statements binding the atomic update of the function [self], whose atomic contract
    has the preconditions [pres] and postconditions [posts], and whose implicit parameters
    are [implicit]; [result] is the contract's name for the result, if there is one. Sets
    [ctx.au]. A step inside the update unfolds the predicates of [pres], and folds those
    of [posts] if it commits, and those of [pres] if it aborts. *)
let atomic_update ctx env ~at ~self ~role ~result implicit ~pres ~posts ~past_results =
  let phi = Names.fresh ctx.names "phi" in
  let au_call ~l f args =
    R.Expr.call ~loc:l (name ~loc:l f) (R.Expr.var ~loc:l (name ~loc:l phi) :: args)
  in
  (* The contract's environment, with the values of the implicit parameters in the
     update, and the result's. *)
  let opened ?value values =
    let env =
      List.fold2_exn implicit values ~init:env ~f:(fun env (x, _, _, _) v ->
          bind env x (Value v))
    in
    match (result, value) with Some r, Some v -> bind env r (Value v) | _ -> env
  in
  let each terms ~at make env =
    let* stmts = all terms ~f:(uses ctx env ~at make) in
    Ok (List.concat stmts)
  in
  let fold ~loc ~pred:_ p args = [ R.Stmt.fold ~loc p args ] in
  let unfold ~loc ~pred:_ p args = [ R.Stmt.unfold ~loc p args ] in
  let open_ ~at ~unfold:with_unfold =
    let l = loc at in
    let* decls =
      all implicit ~f:(fun (x, _, t, _) ->
          let* typ = typ ctx ~at t in
          let v = Names.fresh ctx.names x in
          Ok
            ( R.Stmt.local ~loc:l ~ghost:true ~const:false ~typ (ident ~loc:l v),
              R.Expr.var ~loc:l (name ~loc:l v) ))
    in
    let values = List.map decls ~f:snd in
    let opening =
      match values with
      | [] -> R.Stmt.call ~loc:l (au_call ~l "openAU" [])
      | _ -> R.Stmt.assign ~loc:l values (R.Stmt.expr_rhs (au_call ~l "openAU" []))
    in
    let* unfolds = if with_unfold then each pres ~at unfold (opened values) else Ok [] in
    let invariants = if with_unfold then use_invariants ctx ~at ~fold:false else [] in
    Ok (invariants @ List.concat_map decls ~f:fst @ [ opening ] @ unfolds, values)
  in
  let rec au =
    {
      state = Pending;
      cas_results = [];
      read_results = [];
      values = [];
      step = at;
      performing = None;
      self;
      role;
      ghost_results =
        List.concat_map past_results ~f:(fun (_, _, _, (snapshot, k)) -> [ snapshot; k ]);
      has_result = Option.is_some result;
      open_;
      close;
      token = R.Expr.var ~loc:(loc at) (name ~loc:(loc at) phi);
      commit_only;
    }
  and commit_only ~at ~value =
    let l = loc at in
    let* decls =
      all implicit ~f:(fun (x, _, t, _) ->
          let* typ = typ ctx ~at t in
          let v = Names.fresh ctx.names x in
          Ok
            ( R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l v),
              R.Expr.var ~loc:l (name ~loc:l v) ))
    in
    let values = List.map decls ~f:snd in
    let opening =
      match values with
      | [] -> R.Stmt.call ~loc:l (au_call ~l "openAU" [])
      | _ -> R.Stmt.assign ~loc:l values (R.Stmt.expr_rhs (au_call ~l "openAU" []))
    in
    let* unfolds = each pres ~at unfold (opened values) in
    let* folds = each posts ~at (with_views ctx fold) (opened ~value values) in
    ctx.origins :=
      {
        at;
        code = Commit;
        message =
          "The atomic postcondition may not hold after this step, which linearizes the \
           function";
        related =
          List.map posts ~f:(fun (t : S.term) -> (t.term_loc, "The atomic postcondition"));
      }
      :: !(ctx.origins);
    Ok
      (List.concat_map decls ~f:fst @ [ opening ] @ unfolds @ folds
      @ [ R.Stmt.call ~loc:l (au_call ~l "commitAU" [ value ]) ])
  and close c ~value =
    let at = au.step in
    let l = loc at in
    let value =
      match au.ghost_results with
      | [] -> value
      | ghosts -> R.Expr.tuple ~loc:l ((if au.has_result then [ value ] else []) @ ghosts)
    in
    let commit = R.Stmt.call ~loc:l (au_call ~l "commitAU" [ value ]) in
    (* The facts that the function ensures about the state after the action. *)
    let established performs =
      all past_results ~f:(fun ((p : past), st, _, (snapshot, k)) ->
          match
            ( performs,
              List.Assoc.find ctx.opened p.inv ~equal:String.equal,
              List.Assoc.find ctx.invariants p.inv ~equal:String.equal )
          with
          | Some performed, Some opened, Some args ->
              let next, indices, _ =
                next_state ctx st ~inv_params:st.params args opened performed
              in
              let index =
                match
                  List.Assoc.find indices
                    (List.Assoc.find_exn st.chains p.field ~equal:String.equal)
                    ~equal:String.equal
                with
                | Some index -> index
                | None -> List.Assoc.find_exn opened.indices p.field ~equal:String.equal
              in
              let* e = formula env p.element in
              Ok
                [
                  R.Stmt.assign ~loc:l [ snapshot ]
                    (R.Stmt.expr_rhs
                       (state_of ~loc:l st (grown st (List.map next ~f:fst))));
                  R.Stmt.assign ~loc:l [ k ]
                    (R.Stmt.expr_rhs (R.Expr.index ~loc:l index e));
                ]
          | _ ->
              error at
                "This step linearizes the function, which ensures a fact about the state \
                 after it, but performs no action")
    in
    match c with
    | Commit ->
        let message =
          "The atomic postcondition may not hold after this step, which linearizes the \
           function"
        in
        ctx.origins :=
          {
            at;
            code = Fold;
            message;
            related =
              List.map posts ~f:(fun (t : S.term) ->
                  (t.term_loc, "This part of the atomic postcondition may not hold"));
          }
          :: {
               at;
               code = Commit;
               message;
               related =
                 List.map posts ~f:(fun (t : S.term) ->
                     (t.term_loc, "The atomic postcondition"));
             }
          :: !(ctx.origins);
        let* folds =
          match au.performing with
          | Some (a, _) ->
              (* The views follow from the action; the postcondition's other predicates
                 are folded as usual. *)
              let others ~loc ~pred p args =
                if List.Assoc.mem ctx.shared.views pred ~equal:String.equal then []
                else fold ~loc ~pred p args
              in
              let* views = perform_views ctx ~at a in
              let* others = each posts ~at others (opened ~value au.values) in
              Ok (views @ others)
          | None -> each posts ~at (with_views ctx fold) (opened ~value au.values)
        in
        (* The step is the action's, if its step says when. *)
        let performs = Option.map au.performing ~f:fst in
        let checked =
          match au.performing with
          | Some (p, Some condition) ->
              [
                check ctx ~at
                  (Printf.sprintf "This step may not perform the action %s"
                     p.performed.action)
                  condition;
              ]
          | _ -> []
        in
        let* established = established performs in
        Ok
          (checked @ folds @ List.concat established @ [ commit ]
          @ use_invariants ?performs ctx ~at ~fold:true)
    | Abort ->
        let* folds = each pres ~at fold (opened au.values) in
        Ok
          (folds
          @ [ R.Stmt.call ~loc:l (au_call ~l "abortAU" []) ]
          @ use_invariants ctx ~at ~fold:true)
    | Commit_call -> Ok [ commit ]
  in
  ctx.au <- Some au;
  let l = loc at in
  Ok
    (R.Stmt.local ~loc:l ~ghost:true ~const:true
       ~init:(R.Stmt.expr_rhs (R.Expr.call ~loc:l (name ~loc:l "bindAU") []))
       (ident ~loc:l phi))

(** The invariants that the conjunctions [terms] apply, with their arguments. *)
let invariant_apps ?(include_opaque = false) ctx env (terms : S.term list) =
  let rec apps (t : S.term) =
    let t = S.chain t in
    match spine t [] with
    | { term_desc = Tvar (Qid { pid_str = "&&" | "/\\"; _ }); _ }, [ a; b ] ->
        apps a @ apps b
    | { term_desc = Tvar q; _ }, args ->
        let key = logical_key env q in
        begin match List.Assoc.find ctx.preds key ~equal:String.equal with
        | Some (raven, _)
          when List.Assoc.mem ctx.shared.persistent
                 (canonical_member ctx.shared raven)
                 ~equal:String.equal
               && (include_opaque
                  || not
                       (List.mem ctx.proof_support.opaque_predicates key
                          ~equal:String.equal)) ->
            [ (key, args) ]
        | _ -> []
        end
    | _ -> []
  in
  all (List.concat_map terms ~f:apps) ~f:(fun (p, args) ->
      let raven, _ = List.Assoc.find_exn ctx.preds p ~equal:String.equal in
      let* args = all args ~f:(formula env) in
      Ok (canonical_member ctx.shared raven, args))

(** Initializer bindings are local to the state record and its establishment. *)
let rec initial_bindings env initialization continuation =
  match initialization with
  | S.Initial_record fields -> continuation env fields
  | Initial_let (pattern, rhs, body) ->
      proof_binding ~ghost_rhs:true env pattern rhs (fun env ->
          initial_bindings env body continuation)

let initializer_annotation ctx (f : func) =
  let window (a : Annotation.t) =
    a.loc.loc_start.pos_cnum >= f.body.exp_loc.loc_end.pos_cnum
    && Option.for_all f.next ~f:(fun next ->
        a.loc.loc_end.pos_cnum <= next.loc_start.pos_cnum)
    && Poly.equal (Annotation.kind a) Annotation.Initially
  in
  match List.filter ctx.annotations ~f:window with
  | [] -> Ok None
  | [ a ] -> Result.map (Annotation.initially a) ~f:(fun initial -> Some (a, initial))
  | _ :: a :: _ -> error a.loc "A constructor has at most one initially annotation"

let check_initial_fields ctx established fields =
  let known =
    List.concat_map ctx.shared.structures ~f:(fun st ->
        if List.exists established ~f:(fun (inv, _) -> String.equal inv st.invariant) then
          List.map st.fields ~f:(fun (field, _, _, _, _) -> field)
        else [])
  in
  let rec check seen = function
    | [] -> Ok ()
    | ((id : S.id), _) :: rest ->
        if List.mem seen id.pid_str ~equal:String.equal then
          error id.pid_loc
            (Printf.sprintf "The initial field %s is given twice" id.pid_str)
        else if not (List.mem known id.pid_str ~equal:String.equal) then
          error id.pid_loc (Printf.sprintf "Unknown initial state field %s" id.pid_str)
        else if List.count known ~f:(String.equal id.pid_str) > 1 then
          error id.pid_loc
            (Printf.sprintf
               "The initial field %s belongs to several established invariants" id.pid_str)
        else check (id.pid_str :: seen) rest
  in
  check [] fields

(** The statements establishing the invariant [inv] with [args] at the end of [f], at
    [at]: with the initial state of its structure, as [f]'s annotation
    [(*@ initially { ... } *)] gives it, the history of that state and the index maps of
    its fields owned by index. *)
let establish_invariant ctx ~(f : func) ~at ~env ~initial inv args =
  let l = loc at in
  match List.find ctx.shared.structures ~f:(fun st -> String.equal st.invariant inv) with
  | None -> Ok [ R.Stmt.fold ~loc:l (qualified_name ~loc:l inv) args ]
  | Some st ->
      begin match initial with
      | None when (not (has_history st)) && List.is_empty st.chains ->
          (* The witnesses are computed. *)
          Ok [ R.Stmt.fold ~loc:l (qualified_name ~loc:l inv) args ]
      | None ->
          error f.loc
            (Printf.sprintf
               "This function establishes %s, whose initial state it gives as (*@ \
                initially { ... } *)"
               inv)
      | Some ((a : Annotation.t), initial) ->
          let* values =
            all st.fields ~f:(fun (field, raven, _, t, _) ->
                match
                  List.find initial ~f:(fun (x, _) -> String.equal x.S.pid_str field)
                with
                | Some (_, term) ->
                    let* v = expected_formula env (Some t) term in
                    Ok (raven, v, term)
                | None
                  when List.exists st.pendings ~f:(fun p ->
                           String.equal p.pending_field field) ->
                    (* No calls wait yet. *)
                    Ok (raven, R.Expr.set ~loc:l [], S.mk_term Ttrue a.loc)
                | None ->
                    error a.loc (Printf.sprintf "The initial state has no field %s" field))
          in
          (* The index map of a field owned by index, given as a list of entries. *)
          let rec entries (t : S.term) =
            match spine t [] with
            | { term_desc = Tvar (Qid { pid_str = "[]"; _ }); _ }, [] -> Some []
            | { term_desc = Tvar (Qid { pid_str = "::"; _ }); _ }, [ h; rest ] ->
                Option.map (entries rest) ~f:(fun rest -> h :: rest)
            | _ -> None
          in
          let* indexed =
            all st.chains ~f:(fun (field, index) ->
                let _, entries_value, term =
                  List.find_exn values ~f:(fun (raven, _, _) ->
                      String.equal raven (st.state ^ "_" ^ field))
                in
                match entries term with
                | Some es ->
                    let* es = all es ~f:(formula env) in
                    Ok
                      ( [],
                        ( ident ~loc:l index,
                          R.Expr.map_literal ~loc:l
                            (List.mapi es ~f:(fun i e -> (e, R.Expr.int ~loc:l i)))
                            (R.Expr.int ~loc:l 0) ) )
                | None ->
                    ctx.shared.dynamic_indices <- true;
                    let l = loc term.term_loc in
                    let target = Names.fresh ctx.names "initial_index" in
                    let index_type =
                      R.Type.map ~loc:l (R.Type.ref ~loc:l) (R.Type.int ~loc:l)
                    in
                    ctx.origins :=
                      {
                        at = term.term_loc;
                        code = Precondition;
                        message = "The cells of this indexed field may not be distinct";
                        related = [];
                      }
                      :: !(ctx.origins);
                    Ok
                      ( R.Stmt.local ~loc:l ~ghost:true ~typ:index_type
                          ~init:
                            (R.Stmt.expr_rhs
                               (Indexed_initialization.call ~loc:l entries_value))
                          (ident ~loc:l target),
                        (ident ~loc:l index, R.Expr.var ~loc:l (name ~loc:l target)) ))
          in
          let index_statements, indices = List.unzip indexed in
          (* The keys of no registrations. *)
          let ons =
            List.map st.pendings ~f:(fun p ->
                ( ident ~loc:l p.pending_on,
                  R.Expr.map_literal ~loc:l [] (R.Expr.null ~loc:l) ))
          in
          let history =
            if has_history st then
              let qn m x = generated_module_member ~loc:l m x in
              let full s =
                R.Expr.call ~loc:l
                  (qn (module_name st "history") "full")
                  [ R.Expr.call ~loc:l (qn (module_name st "states") "set") [ s ] ]
              in
              let state =
                R.Expr.call ~loc:l
                  (qn (module_name st "state") "state")
                  (grown st (List.map values ~f:(fun (_, v, _) -> v)))
              in
              let location =
                match anchor ctx.types st.structure_type with
                | Some (_, at) ->
                    R.Expr.field ~loc:l
                      (at ~loc:l (List.hd_exn args))
                      (qualified_name ~loc:l (member_name st "history"))
                | None -> List.hd_exn args
              in
              [
                R.Stmt.call ~loc:l
                  (R.Expr.call ~loc:l (name ~loc:l "fpu")
                     [
                       location;
                       full (R.Expr.set ~loc:l []);
                       full
                         (R.Expr.call ~loc:l
                            (qualified_name ~loc:l (member_name st "states"))
                            [ state ]);
                     ]);
              ]
            else []
          in
          Ok
            (List.concat index_statements @ history
            @ [
                R.Stmt.fold ~loc:l
                  ~witnesses:
                    (List.map values ~f:(fun (raven, v, _) -> (ident ~loc:l raven, v))
                    @ indices @ ons)
                  (qualified_name ~loc:l inv) args;
              ])
      end

(** The procedure of [f], named [proc_name]; if [f] is pure, its result is the value of
    its function. [funcs] are the functions contracts can call, by their OCaml names. *)
let proc types ~refs ~primitives ~shared ~ocaml_env ~preds ~funcs ~annotations
    ~access_proofs ~return_proofs ~initializations ~linearizations ~lifted ~pasts
    ~past_structures ~past_returns ~ghost_args ~procedure_signatures ~libraries
    ~proof_lemmas ~proof_support ~predicate_bodies (functions : string Path_bindings.t)
    origins ~proc_name ~pure ?declaration_name ?pure_name ?(primitive_namespace = [])
    (f : func) : (R.Callable.t, error) Result.t =
  let names = Names.create () in
  let ctx =
    {
      types;
      refs;
      primitives;
      primitive_namespace;
      names;
      functions;
      lifted;
      pasts;
      past_returns;
      ghost_args;
      procedure_signatures;
      ghost_returns = [];
      proof_state = None;
      return_covered = false;
      libraries;
      origins;
      annotations;
      spec_funcs = funcs;
      proof_lemmas;
      proof_support;
      predicate_bodies;
      env = ocaml_env;
      preds;
      facts = [];
      au = None;
      current_procedure = Some proc_name;
      manual = f.manual;
      access_proofs;
      return_proofs;
      initializations;
      linearizations;
      shared;
      invariants = [];
      opened = [];
      snapshots = [];
      positions = [];
      formals = [];
      fields_of = [];
    }
  in
  let l = loc f.loc in
  (* Facts about earlier states are ghost parameters and results. *)
  let split terms =
    List.partition_map terms ~f:(fun t ->
        match past_of past_structures t with Some p -> First p | None -> Second t)
  in
  let past_pres, past_posts, f =
    match f.contract with
    | Some c ->
        let past_pres, requires = split c.requires in
        let past_posts, ensures = split c.ensures in
        (past_pres, past_posts, { f with contract = Some { c with requires; ensures } })
    | None -> ([], [], f)
  in
  let header = Option.bind f.contract ~f:(fun c -> c.header) in
  let* result_name, arg_names = contract_names f header (List.length f.params) in
  let* formals = formals ~names:arg_names ctx f in
  let* bound = pattern_params ctx f formals in
  List.iter
    (List.zip_exn (List.zip_exn f.params arg_names) formals)
    ~f:(fun ((parameter, source), (formal, _, _)) ->
      match (parameter.Typedtree.fp_kind, source, formal) with
      | ( Tparam_pat { pat_desc = Tpat_var _ | Tpat_record _ | Tpat_tuple _; pat_type; _ },
          Some source,
          Some (_, raven) )
        when not (List.Assoc.mem ctx.names.scope source ~equal:String.equal) ->
          ctx.names.scope <- (source, (raven, Some pat_type)) :: ctx.names.scope
      | _ -> ());
  ctx.formals <-
    List.map formals ~f:(fun (ocaml, _, _) ->
        match ocaml with
        | Some (_, x) -> R.Expr.var ~loc:l (name ~loc:l x)
        | None -> unit_value ~loc:l);
  let result = Names.fresh names result_name in
  let* returns =
    if is_unit f.body.exp_type then Ok []
    else
      let* typ = typ ctx ~at:f.body.exp_loc f.body.exp_type in
      Ok [ R.Var.make ~loc:l (ident ~loc:l result) typ ]
  in
  let* _, env, implicit, ghosts = contract_env ctx ~spec_funcs:funcs f formals ~result in
  let* ghost_returns =
    all (ghost_results f) ~f:(fun (id, _) ->
        match
          ( List.Assoc.find env.vars id.pid_str ~equal:String.equal,
            List.Assoc.find env.var_types id.pid_str ~equal:String.equal )
        with
        | Some (Raven raven), Some t -> Ok (id.pid_str, raven, t)
        | _ -> error id.pid_loc "Cannot resolve this ghost result")
  in
  ctx.ghost_returns <- ghost_returns;
  let* ghost_return_vars =
    all ghost_returns ~f:(fun (_, raven, t) ->
        let* typ = typ ctx ~at:f.loc t in
        Ok (R.Var.make ~loc:l ~ghost:true (ident ~loc:l raven) typ))
  in
  let* ghost_formals =
    all ghosts ~f:(fun (_, raven, t) ->
        let* typ = typ ctx ~at:f.loc t in
        Ok (R.Var.make ~loc:l ~ghost:true (ident ~loc:l raven) typ))
  in
  (* A parameter that a precondition makes a field of a ghost parameter is one. *)
  List.iter
    (field_equations (Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires)))
    ~f:(fun (x, field, g) ->
      let position =
        List.findi arg_names ~f:(fun _ n -> Option.equal String.equal n (Some x))
      in
      match (List.find ghosts ~f:(fun (n, _, _) -> String.equal n g), position) with
      | Some (_, ghost, _), Some (i, _) ->
          begin match List.nth formals i with
          | Some (Some (_, raven), _, _) ->
              ctx.fields_of <-
                (raven, (field, R.Expr.var ~loc:l (name ~loc:l ghost))) :: ctx.fields_of
          | _ -> ()
          end
      | _ -> ());
  (* Ghost statements and invariants in the code can use ghost parameters. *)
  List.iter ghosts ~f:(fun (x, raven, t) ->
      ctx.names.scope <- (x, (raven, Some t)) :: ctx.names.scope);
  List.iter implicit ~f:(fun (x, raven, t, _) ->
      ctx.names.scope <- (x, (raven, Some t)) :: ctx.names.scope);
  let implicit_decls = implicit in
  let implicit = List.map implicit ~f:(fun (_, _, _, var) -> var) in
  let specs fs =
    all fs ~f:(fun f -> Result.map (formula env f) ~f:(fun e -> R.Spec.make e))
  in
  (* Values of type [int] are in its range. *)
  let in_range = List.filter_map formals ~f:(fun (_, range, _) -> range) in
  let result_in_range =
    if List.is_empty returns then None else range_spec ~loc:l f.body.exp_type result
  in
  let pres = Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires) in
  let* requires = specs pres in
  (* The invariants of the precondition are opened around each atomic step. *)
  let* invariants = invariant_apps ctx env pres in
  ctx.invariants <- (if f.manual then [] else invariants);
  (* A snapshot and a position witnessing each fact about an earlier state. *)
  let* history_invariants = invariant_apps ~include_opaque:true ctx env pres in
  let witnesses (p : past) =
    let* st =
      match
        List.find shared.structures ~f:(fun st -> String.equal st.invariant p.inv)
      with
      | Some st -> Ok st
      | None -> error p.element.term_loc "A fact about an earlier state without a state"
    in
    let* structure =
      match List.Assoc.find history_invariants p.inv ~equal:String.equal with
      | Some (x :: _) ->
          let anchored =
            match anchor types st.structure_type with
            | Some (_, at) -> at ~loc:l x
            | None -> x
          in
          Ok
            (R.Expr.field ~loc:l anchored
               (qualified_name ~loc:l (member_name st "history")))
      | _ ->
          error p.element.term_loc
            (Printf.sprintf
               "A fact about an earlier state of %s, which the precondition does not hold"
               p.inv)
    in
    let snapshot = Names.fresh names "snapshot" and k = Names.fresh names "position" in
    let var x = R.Expr.var ~loc:l (name ~loc:l x) in
    let* e = formula env p.element in
    let decl x typ = R.Var.make ~loc:l ~ghost:true (ident ~loc:l x) typ in
    Ok
      ( ( p,
          st,
          e,
          [
            decl snapshot
              (R.Type.named ~loc:l
                 (generated_module_member ~loc:l (module_name st "state") "T")
                 []);
            decl k (R.Type.int ~loc:l);
          ],
          (var snapshot, var k) ),
        R.Spec.make
          (past_fact ~loc:l st ~structure ~field:p.field ~snapshot:(var snapshot)
             ~k:(var k) e) )
  in
  let* past_params = all past_pres ~f:witnesses in
  let* past_results = all past_posts ~f:witnesses in
  let past_formals = List.concat_map past_params ~f:(fun ((_, _, _, d, _), _) -> d) in
  let past_returns = List.concat_map past_results ~f:(fun ((_, _, _, d, _), _) -> d) in
  ctx.positions <-
    List.map past_params ~f:(fun ((p, _, e, _, (snapshot, k)), _) ->
        {
          pos_inv = p.inv;
          pos_field = p.field;
          pos_element = e;
          pos_snapshot = snapshot;
          pos_k = k;
        });
  let atomic = Option.exists f.contract ~f:(fun c -> c.atomic) in
  let* () =
    if f.manual && f.trusted then error f.loc "A manual proof cannot also be trusted"
    else Ok ()
  in
  let atomic_pres =
    Option.value_map f.contract ~default:[] ~f:(fun c -> c.atomic_requires)
  in
  let* atomic_requires =
    all atomic_pres ~f:(fun t ->
        Result.map (formula env t) ~f:(fun e -> R.Spec.make ~atomic:true e))
  in
  (* Preconditions without [own] only mention immutable variables, so they hold
     throughout, as in loops. *)
  let* facts =
    specs
      (List.filter pres ~f:(fun t ->
           not (List.mem (term_names t) "own" ~equal:String.equal)))
  in
  ctx.facts <- facts;
  (* Names free in the postconditions are existentially quantified, as [j] in
     [ensures own c.count j]. *)
  let postconditions = contract_postconditions env ~at:f.loc in
  let* ensures =
    postconditions (Option.value_map f.contract ~default:[] ~f:(fun c -> c.ensures))
  in
  let atomic_posts =
    Option.value_map f.contract ~default:[] ~f:(fun c -> c.atomic_ensures)
  in
  let* atomic_ensures = postconditions ~atomic:true atomic_posts in
  let* bind_au =
    if atomic && not f.manual then
      atomic_update ctx env ~at:f.loc ~self:proc_name
        ~role:(Option.value f.role ~default:f.id)
        ~result:(Option.some_if (not (List.is_empty returns)) result_name)
        implicit_decls ~pres:atomic_pres ~posts:atomic_posts
        ~past_results:
          (List.map past_results ~f:(fun ((p, st, _, d, w), _) -> (p, st, d, w)))
    else Ok []
  in
  let* () =
    match Option.value_map f.contract ~default:[] ~f:(fun c -> c.variant) with
    | [] -> Ok ()
    | v :: _ -> unsupported v.term_loc "A variant"
  in
  (* The value of a pure function's function. *)
  let defined =
    if pure && List.is_empty f.signature_sites && not (List.is_empty returns) then
      let args =
        List.map formals ~f:(fun (ocaml, _, _) ->
            match ocaml with
            | Some (_, x) -> R.Expr.var ~loc:l (name ~loc:l x)
            | None -> unit_value ~loc:l)
      in
      [
        R.Spec.make
          (R.Expr.binary ~loc:l Eq
             (R.Expr.var ~loc:l (name ~loc:l result))
             (R.Expr.call ~loc:l
                (Qualified_name.raven ~loc:l
                   (Option.value pure_name
                      ~default:Qualified_name.{ path = []; name = f.raven_name }))
                args));
      ]
    else []
  in
  let requires = in_range @ requires @ List.map past_params ~f:snd @ atomic_requires in
  let ensures =
    Option.to_list result_in_range
    @ defined @ ensures @ List.map past_results ~f:snd @ atomic_ensures
  in
  let all_formals =
    List.map formals ~f:(fun (_, _, v) -> v) @ ghost_formals @ past_formals @ implicit
  in
  if f.trusted then begin
    (* Its contract, assumed: the body is not translated. *)
    Report.warn f.loc
      (Printf.sprintf "%s is trusted: its contract is assumed, not verified"
         (Ident.name f.id));
    Ok
      (R.Callable.proc ~loc:l ~formals:all_formals
         ~returns:(returns @ ghost_return_vars @ past_returns)
         ~requires ~ensures
         (ident ~loc:l (Option.value declaration_name ~default:proc_name))
         None)
  end
  else
    let* first = ghost ctx ~after:f.loc.loc_start ~before:f.body.exp_loc.loc_start in
    let* stmts, v = expr ~tail:true ~keep_scope:true ctx f.body in
    let* finish = finish_arm ctx ~tail:true v in
    let stmts = stmts @ finish in
    let assignment =
      if List.is_empty returns then []
      else
        [
          R.Stmt.assign ~loc:l
            [ R.Expr.var ~loc:l (name ~loc:l result) ]
            (R.Stmt.expr_rhs v);
        ]
    in
    (* The ghost statements after the body follow the result's assignment, and can use its
     name. *)
    ctx.names.scope <- (result_name, (result, Some f.body.exp_type)) :: ctx.names.scope;
    let* last =
      ghost ctx ~after:f.body.exp_loc.loc_end
        ~before:
          (Option.value_map f.next
             ~default:{ f.loc.loc_end with pos_cnum = Int.max_value } ~f:(fun l ->
               l.loc_start))
    in
    let* () =
      match au_state ctx with
      | None | Some Committed -> Ok ()
      | Some Pending ->
          error f.loc
            "This function may return before it linearizes: no step commits its atomic \
             contract"
      | Some Partly ->
          error f.loc
            "This function may return before it linearizes, on some path: annotate the \
             step that linearizes it there, as (*@ commit *) or (*@ returning [] -> \
             commit *)"
      | Some (Registered _) ->
          error f.loc
            "This function may return waiting to be helped: a step after it waits \
             collects its result, as (*@ returning Nil -> commit true *)"
      | Some (Committing | On_cas | On_read _ | Unknown) ->
          error f.loc "Caravan cannot tell whether this function linearizes on every path"
    in
    (* An invariant that the function establishes, as one creating a structure, is folded at
     its end, after setting the views of its postcondition. *)
    let* establish =
      if f.manual then Ok []
      else
        let posts = Option.value_map f.contract ~default:[] ~f:(fun c -> c.ensures) in
        let* established = invariant_apps ctx env posts in
        let established =
          List.filter established ~f:(fun (p, _) ->
              not (List.exists invariants ~f:(fun (q, _) -> String.equal p q)))
        in
        if List.is_empty established then Ok []
        else
          let only_views ~loc ~pred p args =
            if List.Assoc.mem ctx.shared.views pred ~equal:String.equal then
              [ R.Stmt.fold ~loc p args ]
            else []
          in
          let* views =
            all posts ~f:(uses ctx env ~at:f.loc (with_views ctx only_views))
          in
          (* Reported at the end of the function. *)
          let at = { f.loc with loc_start = f.loc.loc_end } in
          List.iter established ~f:(fun (inv, _) ->
              ctx.origins :=
                {
                  at;
                  code = Fold;
                  message =
                    Printf.sprintf
                      "The invariant %s may not hold when this function returns" inv;
                  related =
                    Option.to_list
                      (Option.map
                         (List.Assoc.find ctx.shared.persistent inv ~equal:String.equal)
                         ~f:(fun def -> (def, "The invariant")));
                }
                :: !(ctx.origins));
          let establish initial_env initial =
            let* folds =
              all established ~f:(fun (inv, args) ->
                  establish_invariant ctx ~f ~at ~env:initial_env ~initial inv args)
            in
            Ok (List.concat views @ List.concat folds)
          in
          let* annotated = initializer_annotation ctx f in
          match annotated with
          | None -> establish (scope_env ctx) None
          | Some (annotation, initial) ->
              initial_bindings (scope_env ctx) initial (fun initial_env fields ->
                  let* () = check_initial_fields ctx established fields in
                  establish initial_env (Some (annotation, fields)))
    in
    let history_returns =
      List.filter_map past_results ~f:(fun ((p, _, element, _, (snapshot, index)), _) ->
          Option.map (known_position ctx p.inv p.field element) ~f:(fun position ->
              R.Stmt.assign ~loc:l [ snapshot; index ]
                (R.Stmt.expr_rhs
                   (R.Expr.tuple ~loc:l [ position.pos_snapshot; position.pos_k ]))))
    in
    let body =
      bind_au @ bound @ first @ stmts @ assignment @ establish @ last @ history_returns
    in
    Ok
      (R.Callable.proc ~loc:l ~formals:all_formals
         ~returns:(returns @ ghost_return_vars @ past_returns)
         ~requires ~ensures
         (ident ~loc:l (Option.value declaration_name ~default:proc_name))
         (Some body))

(** The entry [element] of a fact that [f] ensures about an earlier state, given the
    arguments of a call: a parameter, which [names] names, or the argument of a
    constructor that a precondition matches a parameter with, as [c] in
    [requires node === Next (v, c)]. *)
let entry_of_args types (f : func) (names : string option list) (element : S.term) =
  let l = R.Loc.none in
  let param x =
    Option.map
      (List.findi names ~f:(fun _ n -> Option.equal String.equal n (Some x)))
      ~f:fst
  in
  let requires = Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires) in
  let rec conjuncts (t : S.term) =
    match spine (S.chain t) [] with
    | { term_desc = Tvar (Qid { pid_str = "&&" | "/\\"; _ }); _ }, [ a; b ] ->
        conjuncts a @ conjuncts b
    | _ -> [ S.chain t ]
  in
  (* The parameter and destructor of [y], if a precondition matches a parameter with a
     constructor of which [y] is an argument. *)
  let defined y =
    List.find_map (List.concat_map requires ~f:conjuncts) ~f:(fun t ->
        match spine t [] with
        | ( { term_desc = Tvar (Qid { pid_str = "=" | "==" | "==="; _ }); _ },
            [ { term_desc = Tvar (Qid { pid_str = x; _ }); _ }; rhs ] ) ->
            begin match (param x, spine rhs []) with
            | Some i, ({ term_desc = Tvar (Qid { pid_str = c; _ }); _ }, args) -> begin
                let args =
                  match args with [ { term_desc = Ttuple ts; _ } ] -> ts | _ -> args
                in
                match
                  Option.bind
                    (Source.constructor f.environment
                       (S.Qid (S.mk_id ~loc:element.term_loc c)))
                    ~f:(Datatypes.find_cstr types)
                with
                | Some (_, ctor) when List.length ctor.fields = List.length args ->
                    List.find_map (List.zip_exn args ctor.fields) ~f:(fun (a, field) ->
                        match a.S.term_desc with
                        | Tvar (Qid { pid_str = z; _ }) when String.equal z y ->
                            Some (i, field)
                        | _ -> None)
                | _ -> None
              end
            | _ -> None
            end
        | _ -> None)
  in
  match element.term_desc with
  | Tvar (Qid { pid_str = y; _ }) ->
      begin match (param y, defined y) with
      | Some i, _ -> fun args -> List.nth args i
      | None, Some (i, field) ->
          fun args ->
            Option.map (List.nth args i) ~f:(fun a ->
                R.Expr.field ~loc:l a (qualified_name ~loc:l field))
      | None, None -> fun _ -> None
      end
  | _ -> fun _ -> None

(** [funcs], where a function without a contract that a wrapper calls with its own
    parameters first, as [push t value Backoff.default] in [let push t value = ...], has
    the wrapper's contract, and its other parameters are free; it continues the wrapper's
    atomic update. *)
let inherit_contracts (funcs : func list) =
  let param_ids (f : func) =
    Option.all
      (List.map f.params ~f:(fun p ->
           match p.fp_kind with
           | Tparam_pat { pat_desc = Tpat_var (id, _, _); _ } -> Some id
           | _ -> None))
  in
  (* The wrapper of [f], with its contract. *)
  let wrapper (f : func) =
    List.find_map funcs ~f:(fun g ->
        match (g.contract, g.body.exp_desc, param_ids g) with
        | ( Some contract,
            Texp_apply ({ exp_desc = Texp_ident (Pident callee, _, _); _ }, args),
            Some params )
          when Ident.same callee f.id && List.length params <= List.length f.params ->
            let passed =
              List.map
                (List.take args (List.length params))
                ~f:(fun (_, arg) ->
                  match arg with
                  | Typedtree.Arg { exp_desc = Texp_ident (Pident x, _, _); _ } -> Some x
                  | _ -> None)
            in
            Option.some_if
              (List.length passed = List.length params
              && List.for_all2_exn passed params ~f:(fun x p ->
                  Option.exists x ~f:(Ident.same p)))
              (g, contract, List.length params)
        | _ -> None)
  in
  List.map funcs ~f:(fun f ->
      match (f.contract, wrapper f) with
      | None, Some (g, (contract : S.contract), k) ->
          let own_names =
            List.map (List.drop f.params k) ~f:(fun p ->
                match p.fp_kind with
                | Tparam_pat { pat_desc = Tpat_var (id, _, _); pat_loc; _ } ->
                    S.Lvar (S.mk_id ~loc:pat_loc (Ident.name id))
                | _ -> S.Lwild)
          in
          let wrapper_names =
            match contract.header with
            | Some h ->
                List.filter h.hd_args ~f:(function S.Lghost _ -> false | _ -> true)
            | None ->
                List.map (List.take f.params k) ~f:(fun p ->
                    match p.fp_kind with
                    | Tparam_pat { pat_desc = Tpat_var (id, _, _); pat_loc; _ } ->
                        S.Lvar (S.mk_id ~loc:pat_loc (Ident.name id))
                    | _ -> S.Lwild)
          in
          let header =
            {
              S.hd_name = S.mk_id ~loc:f.loc (Ident.name f.id);
              hd_ret =
                Option.value_map contract.header ~default:[ S.Lwild ] ~f:(fun h ->
                    h.hd_ret);
              hd_args = wrapper_names @ own_names;
            }
          in
          {
            f with
            contract = Some { contract with header = Some header };
            role = Some g.id;
          }
      | _ -> f)

(** The value type bound by an argument scheme, without instantiating quantifiers. *)
let argument_value_type t =
  match Types.get_desc t with Tpoly _ -> Btype.tpoly_get_mono_opt t | _ -> Some t

(** The parameters and body of the function [e]: as written, or, for
    [function p1 -> e1 | ...], with its last parameter and a match on it. *)
let function_parts (e : Typedtree.expression) =
  match e.exp_desc with
  | Texp_function (params, Tfunction_body body) -> Some (params, body)
  | Texp_function (params, Tfunction_cases { cases; partial; param; loc; _ }) -> begin
      (* The type of the last parameter, and the result's, after the others. *)
      let rec after n (t : Types.type_expr) =
        match Types.get_desc t with
        | Tarrow (_, a, r, _) ->
            if n = 0 then Option.map (argument_value_type a) ~f:(fun a -> (a, r))
            else after (n - 1) r
        | Tpoly (t, []) -> after n t
        | _ -> None
      in
      match after (List.length params) e.exp_type with
      | None -> None
      | Some (param_type, result_type) ->
          let name = Ident.name param in
          let uid = Shape.Uid.internal_not_actually_unique in
          let pattern : Typedtree.pattern =
            {
              pat_desc = Tpat_var (param, Location.mkloc name loc, uid);
              pat_loc = loc;
              pat_extra = [];
              pat_type = param_type;
              pat_env = e.exp_env;
              pat_attributes = [];
            }
          in
          let fp : Typedtree.function_param =
            {
              fp_arg_label = Nolabel;
              fp_param = param;
              fp_partial = Total;
              fp_kind = Tparam_pat pattern;
              fp_newtypes = [];
              fp_loc = loc;
            }
          in
          let scrutinee : Typedtree.expression =
            {
              e with
              exp_desc =
                Texp_ident
                  ( Pident param,
                    Location.mkloc (Longident.Lident name) loc,
                    {
                      val_type = param_type;
                      val_kind = Val_reg;
                      val_loc = loc;
                      val_attributes = [];
                      val_uid = uid;
                    } );
              exp_loc = loc;
              exp_extra = [];
              exp_type = param_type;
            }
          in
          let cases =
            List.map cases ~f:(fun (c : Typedtree.value Typedtree.case) ->
                { c with c_lhs = Typedtree.as_computation_pattern c.c_lhs })
          in
          let body =
            {
              e with
              exp_desc = Texp_match (scrutinee, cases, [], partial);
              exp_loc = loc;
              exp_extra = [];
              exp_type = result_type;
            }
          in
          Some (params @ [ fp ], body)
    end
  | _ -> None

(** [structure] with the applications by [@@] and [|>] written out, as [f x] for [f @@ x]
    and [x |> f]. *)
let without_application_operators (structure : Typedtree.structure) =
  let expr (mapper : Tast_mapper.mapper) (e : Typedtree.expression) =
    let e = Tast_mapper.default.expr mapper e in
    let apply (f : Typedtree.expression) x =
      match f.exp_desc with
      | Texp_apply (g, args) -> Typedtree.Texp_apply (g, args @ [ (Nolabel, Arg x) ])
      | _ -> Texp_apply (f, [ (Nolabel, Arg x) ])
    in
    match e.exp_desc with
    | Texp_apply
        ({ exp_desc = Texp_ident (p, _, _); _ }, [ (Nolabel, Arg a); (Nolabel, Arg b) ])
      ->
        begin match stdlib_name p with
        | Some "@@" -> { e with exp_desc = apply a b }
        | Some "|>" -> { e with exp_desc = apply b a }
        | _ -> e
        end
    | _ -> e
  in
  let mapper = { Tast_mapper.default with expr } in
  mapper.structure mapper structure

(** The contract annotating the item at [item_loc], ending before [next]: an annotation in
    between. *)
let contract_after ?scope (annotations : Annotation.t list) ~(item_loc : Location.t)
    ~(next : Location.t option) : (S.contract option, error) Result.t =
  let after (a : Annotation.t) =
    Declaration_scope.following ?scope ~item_loc ~next a.loc
  in
  match
    List.filter annotations ~f:(fun a ->
        after a && Poly.equal (Annotation.kind a) Annotation.Contract)
  with
  | [] -> Ok None
  | [ a ] -> Result.map (Annotation.contract a) ~f:Option.some
  | _ :: a :: _ -> error a.loc "A function has at most one contract"

(** Function proof markers follow their declaration, before the next item. *)
let marked_after ?scope (annotations : Annotation.t list) kind ~(item_loc : Location.t)
    ~(next : Location.t option) =
  List.exists annotations ~f:(fun a ->
      Declaration_scope.following ?scope ~item_loc ~next a.loc
      && Poly.equal (Annotation.kind a) kind)

let trusted_after ?scope annotations = marked_after ?scope annotations Annotation.Trusted
let manual_after ?scope annotations = marked_after ?scope annotations Annotation.Manual

(** The contracts of the values of [interface], by their names: an annotation after the
    value's declaration. *)
let interface_contracts (interface : Source.interface) =
  let annotations = Annotation.of_comments interface.interface_comments in
  let items = interface.signature in
  let nexts =
    List.map (List.drop items 1) ~f:(fun (i : Parsetree.signature_item) ->
        Some i.psig_loc)
    @ if List.is_empty items then [] else [ None ]
  in
  let* contracts =
    all (List.zip_exn items nexts) ~f:(fun ((item : Parsetree.signature_item), next) ->
        match item.psig_desc with
        | Psig_value vd ->
            let* contract =
              contract_after ~scope:interface.scope annotations ~item_loc:item.psig_loc
                ~next
            in
            Ok (Option.map contract ~f:(fun c -> (vd.pval_name.txt, (c, item.psig_loc))))
        | _ -> Ok None)
  in
  Ok (List.filter_opt contracts)

(** The data types and functions of [structure], in order, with the contracts of the
    functions in [annotations], or in [interface], by their names. *)
let items source ~fresh (inventory : Module_inventory.t) =
  let* signature_predicates =
    all
      (List.filter inventory.constraints ~f:(fun constraint_ ->
           Option.is_some constraint_.Module_inventory.owner))
      ~f:(fun constraint_ ->
        all constraint_.Module_inventory.signature.signature_resources
          ~f:(fun (name, resource) ->
            let environment = Source.annotation_env source resource.site.environment in
            let* parameters =
              all resource.declaration.pred_params ~f:(fun (id, ty) ->
                  Source.ocaml_type environment ~at:id.S.pid_loc ty)
            in
            Ok
              (List.map constraint_.signature.signature_values ~f:(fun (_, value) ->
                   (value.declaration.val_id, name, parameters)))))
  in
  let signature_predicates = List.concat (List.concat signature_predicates) in
  let* data =
    all inventory.types ~f:(fun (entry : Module_inventory.type_definition) ->
        let* data = Datatypes.of_declaration entry.declaration in
        let data = Datatypes.with_paths data entry.paths in
        let base = String.concat ~sep:"_" (entry.namespace @ [ data.module_name ]) in
        let data = Datatypes.with_name data (fresh base) in
        let heap =
          Option.map data.heap
            ~f:
              (List.map ~f:(fun (field : Datatypes.field) ->
                   { field with raven_field = fresh field.raven_field }))
        in
        Ok { data with heap })
  in
  let same_scope (a : Module_inventory.value) (b : Module_inventory.value) =
    let a = a.site.scope.location and b = b.site.scope.location in
    a.loc_start.pos_cnum = b.loc_start.pos_cnum && a.loc_end.pos_cnum = b.loc_end.pos_cnum
  in
  let* functions =
    all inventory.values ~f:(fun (entry : Module_inventory.value) ->
        let vb = entry.binding in
        match (vb.vb_pat.pat_desc, function_parts vb.vb_expr) with
        | Tpat_var (id, _, _), Some (params, body) ->
            let site = entry.site in
            let* own =
              contract_after ~scope:site.scope site.annotations ~item_loc:site.item_loc
                ~next:site.next
            in
            let* supplied =
              all entry.signatures ~f:(fun (view : Module_inventory.signature_value) ->
                  let site = view.site in
                  let* contract =
                    contract_after ~scope:site.scope site.annotations
                      ~item_loc:site.item_loc ~next:site.next
                  in
                  let* () =
                    match contract with
                    | None -> Ok ()
                    | Some contract ->
                        let* () =
                          Signature_contract.lowerable source view
                            ~environment:
                              (Source.annotation_env source entry.site.environment)
                            contract
                        in
                        Signature_contract.check
                          ~predicates:(function
                            | S.Qid id ->
                                List.find_map signature_predicates
                                  ~f:(fun (value, name, parameters) ->
                                    Option.some_if
                                      (Ident.same value view.declaration.val_id
                                      && String.equal name id.pid_str)
                                      parameters)
                            | Qdot _ -> None)
                          ~restricted:(not (List.is_empty entry.namespace))
                          ~logical_types:source.Source.logical_types source view contract
                  in
                  Ok (Option.map contract ~f:(fun contract -> (contract, site.item_loc))))
            in
            let supplied = List.filter_opt supplied in
            let* contract =
              match (own, supplied) with
              | Some _, (_, at) :: _ ->
                  let root = List.is_empty entry.namespace in
                  error vb.vb_loc
                    ~related:
                      [
                        ( at,
                          if root then "Its contract in the interface"
                          else "Its contract in the signature" );
                      ]
                    (if root then
                       Printf.sprintf
                         "%s has a contract in its interface and another one here"
                         (Ident.name id)
                     else
                       "A function has a contract in its signature and another one here")
              | None, (contract, _) :: [] -> Ok (Some contract)
              | None, [] -> Ok None
              | Some _, []
                when (not (List.is_empty entry.signatures))
                     && not (List.is_empty entry.namespace) ->
                  error vb.vb_loc
                    "An exported module member's contract must be declared in its \
                     signature"
              | Some contract, [] -> Ok (Some contract)
              | None, _ :: (_, at) :: _ ->
                  error at "Multiple contracts for a module member are unsupported"
            in
            let earlier =
              List.take_while inventory.values ~f:(fun other ->
                  not (phys_equal other entry))
            in
            let later = List.drop inventory.values (List.length earlier + 1) in
            let same_name other =
              same_scope entry other
              &&
              match other.Module_inventory.binding.vb_pat.pat_desc with
              | Tpat_var (other, _, _) -> String.equal (Ident.name id) (Ident.name other)
              | _ -> false
            in
            let base =
              if List.is_empty entry.namespace && List.exists later ~f:same_name then
                Printf.sprintf "%s_%d" (Ident.name id)
                  (1 + List.count earlier ~f:same_name)
              else
                String.uncapitalize
                  (String.concat ~sep:"_" (entry.namespace @ [ Ident.name id ]))
            in
            Ok
              {
                id;
                namespace = entry.namespace;
                paths = entry.paths;
                environment =
                  Source.annotation_env source ~at:site.item_loc site.environment;
                signature_sites = entry.signatures;
                raven_name = fresh base;
                params;
                body;
                loc = vb.vb_loc;
                contract;
                next =
                  Some
                    (Option.value site.next
                       ~default:
                         {
                           site.scope.location with
                           loc_start = site.scope.location.loc_end;
                         });
                prefix = [];
                prefix_count = 0;
                captured = [];
                role = None;
                manual =
                  manual_after ~scope:site.scope site.annotations ~item_loc:site.item_loc
                    ~next:site.next;
                trusted =
                  trusted_after ~scope:site.scope site.annotations ~item_loc:site.item_loc
                    ~next:site.next;
              }
        | _ -> unsupported vb.vb_loc "This definition")
  in
  Ok (data, functions)

(** The identifiers that [e] refers to by a name of its own. *)
let referenced (e : Typedtree.expression) : Ident.t list =
  let found = ref [] in
  let expr iterator (e : Typedtree.expression) =
    begin match e.exp_desc with
    | Texp_ident (Pident id, _, _) -> found := id :: !found
    | _ -> ()
    end;
    Tast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Tast_iterator.default_iterator with expr } in
  iterator.expr iterator e;
  !found

(** An iterator collecting the identifiers that patterns bind, and what it found. *)
let binders () =
  let found = ref [] in
  let pat : type k. Tast_iterator.iterator -> k Typedtree.general_pattern -> unit =
   fun iterator p ->
    begin match p.pat_desc with
    | Tpat_var (id, _, _) | Tpat_alias (_, id, _, _, _) ->
        found := (id, p.pat_type, p.pat_loc) :: !found
    | _ -> ()
    end;
    Tast_iterator.default_iterator.pat iterator p
  in
  ({ Tast_iterator.default_iterator with pat }, found)

(** The identifiers that the patterns of [e] bind, with their types and locations. *)
let typed_bound_in (e : Typedtree.expression) =
  let iterator, found = binders () in
  iterator.expr iterator e;
  !found

(** The identifiers that the patterns of [e] bind, its functions' parameters included. *)
let bound_in (e : Typedtree.expression) : Ident.t list =
  List.map (typed_bound_in e) ~f:(fun (id, _, _) -> id)

(** The identifiers that the parameters [params] bind, in order. *)
let params_bound (params : Typedtree.function_param list) : Ident.t list =
  let iterator, found = binders () in
  List.iter params ~f:(fun p ->
      match p.fp_kind with
      | Tparam_pat pat -> iterator.pat iterator pat
      | Tparam_optional_default (pat, _) -> iterator.pat iterator pat);
  List.rev_map !found ~f:(fun (id, _, _) -> id)

(** The local functions of the top-level function [outer], lifted to the top level, with
    their contracts in [annotations]: one after the function's definition, before the
    expression it is local to. A function that [continues] [outer] takes [outer]'s
    parameters first and has its contract too; another may not use [outer]'s variables. *)
let local_functions ~source (outer : func) (annotations : Annotation.t list) =
  let found = ref [] in
  let expr iterator (e : Typedtree.expression) =
    begin match e.exp_desc with
    | Texp_let (_, [ vb ], rest) ->
        begin match (vb.vb_pat.pat_desc, function_parts vb.vb_expr) with
        | Tpat_var (id, _, _), Some (params, body) ->
            found := (vb, id, params, body, rest) :: !found
        | _ -> ()
        end
    | _ -> ()
    end;
    Tast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Tast_iterator.default_iterator with expr } in
  iterator.expr iterator outer.body;
  let outer_params = params_bound outer.params in
  let outer_bound = outer_params @ bound_in outer.body in
  all (List.rev !found)
    ~f:(fun
        ((vb : Typedtree.value_binding), id, params, body, (rest : Typedtree.expression))
      ->
      let* contract =
        contract_after annotations ~item_loc:vb.vb_loc ~next:(Some rest.exp_loc)
      in
      let continues = Option.bind contract ~f:(fun c -> c.continues) in
      let* () =
        match continues with
        | Some g when not (String.equal g.pid_str (Ident.name outer.id)) ->
            error g.pid_loc
              (Printf.sprintf "A local function of %s continues %s only"
                 (Ident.name outer.id) (Ident.name outer.id))
        | _ -> Ok ()
      in
      let prefix = if Option.is_some continues then outer_params else [] in
      let own = (id :: params_bound params) @ bound_in body in
      let captured =
        List.filter (referenced body) ~f:(fun x ->
            List.mem outer_bound x ~equal:Ident.same
            && (not (List.mem own x ~equal:Ident.same))
            && not (List.mem prefix x ~equal:Ident.same))
      in
      (* The variables of its context that the function uses are parameters of it. *)
      let captured = List.dedup_and_sort captured ~compare:Ident.compare in
      let typed =
        let iterator, found = binders () in
        List.iter outer.params ~f:(fun p ->
            match p.fp_kind with
            | Tparam_pat pat -> iterator.pat iterator pat
            | Tparam_optional_default (pat, _) -> iterator.pat iterator pat);
        !found @ typed_bound_in outer.body
      in
      let* captured_params =
        all captured ~f:(fun x ->
            match List.find typed ~f:(fun (y, _, _) -> Ident.same x y) with
            | Some (_, t, at) ->
                let uid = Shape.Uid.internal_not_actually_unique in
                let pattern : Typedtree.pattern =
                  {
                    pat_desc = Tpat_var (x, Location.mkloc (Ident.name x) at, uid);
                    pat_loc = at;
                    pat_extra = [];
                    pat_type = t;
                    pat_env = body.exp_env;
                    pat_attributes = [];
                  }
                in
                Ok
                  {
                    Typedtree.fp_arg_label = Nolabel;
                    fp_param = x;
                    fp_partial = Total;
                    fp_kind = Tparam_pat pattern;
                    fp_newtypes = [];
                    fp_loc = at;
                  }
            | None ->
                error vb.vb_loc
                  (Printf.sprintf
                     "The type of %s, which this local function uses, is unknown"
                     (Ident.name x)))
      in
      let captured_names =
        List.map captured ~f:(fun x -> S.Lvar (S.mk_id ~loc:vb.vb_loc (Ident.name x)))
      in
      (* The contract of the function continued, with its parameters first. *)
      let contract =
        match (contract, continues, outer.contract) with
        | Some c, Some _, Some oc ->
            let names (f_params : Typedtree.function_param list) (h : S.header option) =
              match h with
              | Some h -> h.hd_args
              | None ->
                  List.map f_params ~f:(fun p ->
                      match p.fp_kind with
                      | Tparam_pat { pat_desc = Tpat_var (x, _, _); pat_loc; _ } ->
                          S.Lvar (S.mk_id ~loc:pat_loc (Ident.name x))
                      | _ -> S.Lwild)
            in
            let header =
              {
                S.hd_name = S.mk_id ~loc:vb.vb_loc (Ident.name id);
                hd_ret =
                  Option.value_map c.header ~default:[ S.Lwild ] ~f:(fun h -> h.hd_ret);
                hd_args =
                  names outer.params oc.header @ captured_names @ names params c.header;
              }
            in
            Some
              {
                c with
                header = Some header;
                atomic = oc.atomic;
                requires = oc.requires @ c.requires;
                atomic_requires = oc.atomic_requires;
                atomic_ensures = oc.atomic_ensures;
              }
        | Some c, None, _ ->
            (* Its own contract, which names the variables it uses as they are named. *)
            Some
              (match c.header with
              | Some h ->
                  { c with header = Some { h with hd_args = captured_names @ h.hd_args } }
              | None -> c)
        | _ -> contract
      in
      let prefix_params = if Option.is_some continues then outer.params else [] in
      Ok
        {
          id;
          namespace = outer.namespace;
          paths = [ Path.Pident id ];
          environment = Source.annotation_env source ~at:rest.exp_loc rest.exp_env;
          signature_sites = [];
          raven_name =
            (if List.is_empty outer.namespace then Ident.name id
             else String.concat ~sep:"_" [ outer.raven_name; Ident.name id ]);
          params = prefix_params @ captured_params @ params;
          body;
          loc = vb.vb_loc;
          contract;
          next = Some rest.exp_loc;
          prefix;
          prefix_count = List.length prefix_params;
          captured;
          manual =
            outer.manual
            || manual_after annotations ~item_loc:vb.vb_loc ~next:(Some rest.exp_loc);
          trusted =
            trusted_after annotations ~item_loc:vb.vb_loc ~next:(Some rest.exp_loc);
          role = Option.map continues ~f:(fun _ -> outer.id);
        })

(** The offsets of the ends of the applications of [Atomic]'s operations in [structure].
*)
let atomic_steps (structure : Typedtree.structure) : int list =
  let found = ref [] in
  let expr iterator (e : Typedtree.expression) =
    begin match e.exp_desc with
    | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _)
      when Option.is_some (atomic_name path) ->
        found := step_end e :: !found
    | _ -> ()
    end;
    Tast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Tast_iterator.default_iterator with expr } in
  iterator.structure iterator structure;
  !found

(** Resolves annotations to one source expression, including nested calls. *)
let attached_annotations ?(all_expressions = false) ?(innermost = false)
    (source : Source.t) typed annotations ~kind ~is_target ~description =
  let attached =
    List.filter_map annotations ~f:(fun a ->
        if Poly.equal (Annotation.kind a) kind then
          let rec anchor i =
            if i > 0 && Char.is_whitespace source.text.[i - 1] then anchor (i - 1)
            else
              match
                List.find source.comments ~f:(fun (_, at) ->
                    at.Location.loc_end.pos_cnum = i)
              with
              | Some (_, at) -> anchor at.loc_start.pos_cnum
              | None -> i
          in
          Some (anchor a.loc.loc_start.pos_cnum, a)
        else None)
  in
  let expressions = ref [] in
  let collect_expression iterator (e : Typedtree.expression) =
    let eligible = is_target e in
    if all_expressions then
      begin if eligible then expressions := (e, true) :: !expressions
      end
    else
      begin match e.exp_desc with
      | Texp_apply _ | Texp_record _ -> expressions := (e, eligible) :: !expressions
      | _ -> ()
      end;
    Tast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Tast_iterator.default_iterator with expr = collect_expression } in
  iterator.structure iterator typed;
  let* attached =
    all attached ~f:(fun (anchor, annotation) ->
        let candidates =
          List.filter !expressions ~f:(fun (e, _) ->
              (anchor = step_end e
              &&
              match e.exp_desc with
              | Texp_apply (callee, _) -> anchor >= callee.exp_loc.loc_end.pos_cnum
              | _ -> true)
              || anchor = e.exp_loc.loc_end.pos_cnum
              || List.exists e.exp_extra ~f:(fun (_, at, _) ->
                  anchor = at.loc_end.pos_cnum))
        in
        match
          List.min_elt candidates ~compare:(fun (a, _) (b, _) ->
              match
                Int.compare a.exp_loc.loc_start.pos_cnum b.exp_loc.loc_start.pos_cnum
              with
              | 0 -> Int.compare b.exp_loc.loc_end.pos_cnum a.exp_loc.loc_end.pos_cnum
              | order -> if innermost then -order else order)
        with
        | None | Some (_, false) -> error annotation.loc description
        | Some (expression, true) ->
            Ok
              ( ( expression.exp_loc.loc_start.pos_cnum,
                  expression.exp_loc.loc_end.pos_cnum ),
                annotation ))
  in
  let* () =
    match List.find_a_dup (List.map attached ~f:fst) ~compare:Poly.compare with
    | None -> Ok ()
    | Some start ->
        let annotation = List.Assoc.find_exn attached start ~equal:Poly.equal in
        error annotation.loc "This expression has more than one annotation of this kind"
  in
  Ok attached

let initialization_annotations source typed annotations =
  let is_target (e : Typedtree.expression) =
    match e.exp_desc with
    | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _) ->
        Option.exists (stdlib_name path) ~f:(String.equal "ref")
        || Option.exists (atomic_name path) ~f:(fun op ->
            List.mem [ "make"; "make_contended" ] op ~equal:String.equal)
    | Texp_record { fields; extended_expression = None; _ } ->
        Array.exists fields ~f:(fun (label, _) ->
            Poly.equal label.Data_types.lbl_mut Mutable)
    | _ -> false
  in
  attached_annotations source typed annotations ~kind:Annotation.Initializes ~is_target
    ~description:"This annotation must follow a fresh allocation"

let access_annotations ~libraries ?(checked = []) source typed annotations ~functions =
  let functions =
    Path_bindings.of_list
      (List.concat_map functions ~f:(fun f ->
           List.map f.paths ~f:(fun path -> (path, ()))))
  in
  let functions =
    List.fold checked ~init:functions ~f:(fun functions path ->
        Path_bindings.add functions path ())
  in
  let libraries = library_paths libraries in
  let is_target (e : Typedtree.expression) =
    match e.exp_desc with
    | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _) -> (
        Option.exists (atomic_name path) ~f:(fun op ->
            not (String.is_prefix op ~prefix:"make"))
        ||
        match Source.normalize_value_path e.exp_env ~at:e.exp_loc path with
        | Ok path ->
            Path_bindings.mem functions path
            || Option.is_some (Path_bindings.member libraries path)
        | Error _ -> false)
    | _ -> false
  in
  attached_annotations source typed annotations ~kind:Annotation.Scope ~is_target
    ~description:"Ghost.scope must follow an Atomic access or a checked procedure call"

(** The functions of [funcs] that must be pure: those that contracts call or say are
    [pure], and the functions these call. *)
let pure_functions (funcs : func list) =
  let* () =
    Result.all_unit
      (List.map funcs ~f:(fun f ->
           let clauses =
             Option.value_map f.contract ~default:[] ~f:(fun (c : S.contract) ->
                 c.requires @ c.ensures @ c.atomic_requires @ c.atomic_ensures @ c.variant)
           in
           Result.all_unit
             (List.map clauses ~f:(fun term ->
                  Result.all_unit
                    (List.map
                       (term_references (contract_bound_names f) term)
                       ~f:(fun q ->
                         match Source.value_path f.environment q with
                         | Some (Path.Pdot _ as path)
                           when List.exists funcs ~f:(fun target ->
                                    (not (List.is_empty target.signature_sites))
                                    && List.mem target.paths path ~equal:Path.same) ->
                             unsupported term.term_loc
                               "A specification call through a constrained module \
                                signature"
                         | Some _ | None -> Ok ()))))))
  in
  let referenced_in_contracts =
    List.concat_map funcs ~f:(fun f ->
        Option.value_map f.contract ~default:[] ~f:(fun (c : S.contract) ->
            List.concat_map
              (c.requires @ c.ensures @ c.variant)
              ~f:(fun t ->
                List.filter_map
                  (term_references (contract_bound_names f) t)
                  ~f:(Source.value_path f.environment))))
  in
  let seeds =
    List.filter funcs ~f:(fun f ->
        List.exists f.paths ~f:(fun path ->
            List.mem referenced_in_contracts path ~equal:Path.same)
        || Option.exists f.contract ~f:(fun (c : S.contract) -> c.pure))
  in
  let is_in set f = List.exists set ~f:(fun g -> Ident.same g.id f.id) in
  let references body =
    let paths = ref [] in
    let expr iterator (e : Typedtree.expression) =
      (match e.exp_desc with
      | Texp_ident (path, _, _) -> paths := (e.exp_env, e.exp_loc, path) :: !paths
      | _ -> ());
      Tast_iterator.default_iterator.expr iterator e
    in
    let iterator = { Tast_iterator.default_iterator with expr } in
    iterator.expr iterator body;
    all !paths ~f:(fun (env, at, path) ->
        let* path = Source.normalize_value_path env ~at path in
        let* () =
          match path with
          | Path.Pdot _
            when List.exists funcs ~f:(fun target ->
                     (not (List.is_empty target.signature_sites))
                     && List.mem target.paths path ~equal:Path.same) ->
              unsupported at "A pure call through a constrained module signature"
          | _ -> Ok ()
        in
        Ok path)
  in
  let rec close set =
    let* called = all set ~f:(fun f -> references f.body) in
    let called = List.concat called in
    let added =
      List.filter funcs ~f:(fun f ->
          (not (is_in set f))
          && List.exists f.paths ~f:(fun path -> List.mem called path ~equal:Path.same))
    in
    if List.is_empty added then Ok set else close (set @ added)
  in
  close seeds

(** How a predicate is defined: by a body; as a direct invariant; as an invariant in terms
    of its state's fields; or as a view of an invariant's state. *)
type definition =
  | Body of S.term
  | Direct_invariant of S.term
  | Invariant of {
      state : string;
      fields : S.state_field list;
      body : S.term;
      field_environment : Env.t;
      field_scope : Proof_scopes.scope option;
    }
  | View of { value : S.term }

(** [t], if it owns the entries of a field of the state [state] by index, as
    [forall i. g -> own s.cells.(i) v]: the index, the guard, the field and the value. *)
let chain_of ~state (t : S.term) =
  match t.term_desc with
  | Tquant (Tforall, [ (i, _) ], body) ->
      begin match spine (S.chain body) [] with
      | { term_desc = Tvar (Qid { pid_str = "->"; _ }); _ }, [ guard; owned ] ->
          begin match spine owned [] with
          | { term_desc = Tvar (Qid { pid_str = "own"; _ }); _ }, [ location; value ] ->
              begin match spine location [] with
              | ( { term_desc = Tvar (Qid { pid_str = "([])"; _ }); _ },
                  [
                    {
                      term_desc =
                        Tfield
                          ( { term_desc = Tvar (Qid { pid_str = s; _ }); _ },
                            Qid { pid_str = field; _ } );
                      _;
                    };
                    { term_desc = Tvar (Qid { pid_str = j; _ }); _ };
                  ] )
                when String.equal s state && String.equal j i.S.pid_str ->
                  Some (i, guard, field, value)
              | _ -> None
              end
          | _ -> None
          end
      | _ -> None
      end
  | _ -> None

(** The members generated for the state of [st]: the state of its growing fields as a data
    type, its order, with transitivity, the states it extends, their history as a resource
    algebra and its ghost field, and lemmas taking snapshots of the history and growing
    it. *)
let structure_members types (st : structure) ~at : (R.Member.t list, error) Result.t =
  let l = loc at in
  let n x = R.Name.make ~loc:l x in
  let qn m x = generated_module_member ~loc:l m x in
  let var x = R.Expr.var ~loc:l (n x) in
  let call f args = R.Expr.call ~loc:l f args in
  let bin op a b = R.Expr.binary ~loc:l op a b in
  let state_module = module_name st "state" in
  let state_type = R.Type.named ~loc:l (qn state_module "T") [] in
  let decl x t = R.Var.make ~loc:l (ident ~loc:l x) t in
  let length s = call (qn "Seq" "length") [ s ] in
  let extends a b = call (qualified_name ~loc:l (member_name st "extends")) [ a; b ] in
  let states s = call (qualified_name ~loc:l (member_name st "states")) [ s ] in
  let set_module = module_name st "states"
  and history_module = module_name st "history" in
  let auth s = call (qn history_module "auth") [ call (qn set_module "set") [ s ] ] in
  let history_field = member_name st "history" in
  let* structure_typ = Datatypes.typ types ~at st.structure_type in
  let* anchored =
    match anchor types st.structure_type with
    | Some (_, at) ->
        Ok
          (fun e ->
            R.Expr.field ~loc:l (at ~loc:l e) (qualified_name ~loc:l history_field))
    | None ->
        error at "The structure of a state is a reference: an atomic, a ref or a record"
  in
  let state_data =
    R.Member.module_ ~loc:l
      (generated_ident ~loc:l state_module)
      [
        R.Member.type_ ~loc:l (ident ~loc:l "T")
          (Some
             (R.Type.data ~loc:l
                [
                  R.Type.variant ~loc:l (ident ~loc:l "state")
                    (List.filter_map st.fields ~f:(fun (f, _, typ, _, grows) ->
                         Option.some_if grows (ident ~loc:l f, typ)));
                ]));
      ]
  in
  (* Sequences grow by prefix, pending calls by inclusion, integers by <=. *)
  let order =
    let a = var "a" and b = var "b" in
    let field e f = R.Expr.field ~loc:l e (n f) in
    let grows =
      List.filter_map st.fields ~f:(fun (f, _, _, t, grows) ->
          if not grows then None
          else
            match Datatypes.desc types t with
            | Tconstr (p, [ _ ], _)
              when Option.exists (Datatypes.find types p) ~f:Datatypes.is_sequence ->
                Some
                  (bin And
                     (bin Leq (length (field a f)) (length (field b f)))
                     (bin Eq (field a f)
                        (R.Expr.slice_to ~loc:l (field b f) (length (field a f)))))
            | _ when List.exists st.pendings ~f:(fun p -> String.equal p.pending_field f)
              ->
                Some (bin Subseteq (field a f) (field b f))
            | _ -> Some (bin Leq (field a f) (field b f)))
    in
    Option.value (List.reduce grows ~f:(bin And)) ~default:(R.Expr.bool ~loc:l true)
  in
  let func name formals ret body =
    R.Member.callable
      (R.Callable.func ~loc:l ~formals
         ~returns:[ decl "ret" ret ]
         (generated_ident ~loc:l name) (Some body))
  in
  let lemma ?auto ?triggers name formals ~requires ~ensures body =
    R.Member.callable
      (R.Callable.proc ~loc:l ~kind:Lemma ?auto ~formals
         ~requires:(List.map requires ~f:R.Spec.make)
         ~ensures:(List.map ensures ~f:(R.Spec.make ?triggers))
         (generated_ident ~loc:l name) (Some body))
  in
  let fpu location a b = R.Stmt.call ~loc:l (call (n "fpu") [ location; a; b ]) in
  let x = var "x" and s = var "s" and s1 = var "s1" and s2 = var "s2" in
  let history = anchored x in
  Ok
    ([
       state_data;
       func (member_name st "extends")
         [ decl "a" state_type; decl "b" state_type ]
         (R.Type.bool ~loc:l) order;
       (* Triggered by two steps of the order, as Z3 would choose, but fixed. *)
       lemma ~auto:true
         ~triggers:[ [ extends (var "a") (var "b"); extends (var "b") (var "c") ] ]
         (member_name st "extends_trans")
         [ decl "a" state_type; decl "b" state_type; decl "c" state_type ]
         ~requires:[ bin And (extends (var "a") (var "b")) (extends (var "b") (var "c")) ]
         ~ensures:[ extends (var "a") (var "c") ]
         [];
       func (member_name st "states")
         [ decl "s" state_type ]
         (R.Type.set ~loc:l state_type)
         (R.Expr.set_compr ~loc:l (decl "e" state_type) (extends (var "e") s));
       R.Member.instance ~loc:l
         ~def:(R.Name.make ~loc:l ~path:[ "Library" ] "SetRA", [ state_type ])
         (generated_ident ~loc:l set_module)
         (R.Name.make ~loc:l ~path:[ "Library" ] "SetRA");
       R.Member.instance ~loc:l
         ~def:
           ( R.Name.make ~loc:l ~path:[ "Library" ] "Auth",
             [ R.Type.named ~loc:l (qualified_name ~loc:l set_module) [] ] )
         (generated_ident ~loc:l history_module)
         (R.Name.make ~loc:l ~path:[ "Library" ] "Auth");
       R.Member.field ~loc:l ~ghost:true
         (generated_ident ~loc:l history_field)
         (R.Type.named ~loc:l (qualified_name ~loc:l history_module) []);
       (* Takes note of the current state. *)
       lemma (member_name st "snapshot")
         [ decl "x" structure_typ; decl "s" state_type ]
         ~requires:[ R.Expr.own ~loc:l [ history; auth (states s) ] ]
         ~ensures:
           [
             R.Expr.own ~loc:l
               [
                 history;
                 call
                   (qn history_module "auth_frag")
                   [
                     call (qn set_module "set") [ states s ];
                     call (qn set_module "set") [ R.Expr.set ~loc:l [ s ] ];
                   ];
               ];
           ]
         [
           fpu history
             (auth (states s))
             (call
                (qn history_module "auth_frag")
                [
                  call (qn set_module "set") [ states s ];
                  call (qn set_module "set") [ R.Expr.set ~loc:l [ s ] ];
                ]);
         ];
       (* Moves the history on to a state that extends the current one. *)
       lemma (member_name st "learn")
         [ decl "x" structure_typ; decl "s1" state_type; decl "s2" state_type ]
         ~requires:
           [ bin And (R.Expr.own ~loc:l [ history; auth (states s1) ]) (extends s1 s2) ]
         ~ensures:
           [
             R.Expr.own ~loc:l
               [
                 history;
                 call (qn history_module "full")
                   [ call (qn set_module "set") [ states s2 ] ];
               ];
           ]
         [
           fpu history
             (auth (states s1))
             (call (qn history_module "full")
                [ call (qn set_module "set") [ states s2 ] ]);
         ];
       (* A snapshot precedes the current state. *)
       (let t = var "t" in
        let both =
          R.Expr.own ~loc:l
            [
              history;
              call
                (qn history_module "auth_frag")
                [
                  call (qn set_module "set") [ states t ];
                  call (qn set_module "set") [ R.Expr.set ~loc:l [ s ] ];
                ];
            ]
        in
        lemma (member_name st "observe")
          [ decl "x" structure_typ; decl "s" state_type; decl "t" state_type ]
          ~requires:[ both ]
          ~ensures:[ both; extends s t ]
          []);
     ]
    @ List.map st.chains ~f:(fun (field, _) ->
        (* A later state keeps the entries of an earlier one at their positions. *)
        let t = var "t" and k = var "k" in
        let entries e = R.Expr.field ~loc:l e (n field) in
        let within e =
          bin And (bin Leq (R.Expr.int ~loc:l 0) k) (bin Lt k (length (entries e)))
        in
        lemma
          (member_name st ("kept_" ^ field))
          [ decl "s" state_type; decl "t" state_type; decl "k" (R.Type.int ~loc:l) ]
          ~requires:[ bin And (extends s t) (within s) ]
          ~ensures:
            [
              bin And (within t)
                (bin Eq
                   (R.Expr.index ~loc:l (entries t) k)
                   (R.Expr.index ~loc:l (entries s) k));
            ]
          []))

(** The views that bind the implicit parameters of the function [f] in its atomic
    precondition, as [queue q xs]: the parameter, the view and its ghost field. *)
let view_bindings ctx (f : func) =
  let atomic_requires =
    Option.value_map f.contract ~default:[] ~f:(fun c -> c.atomic_requires)
  in
  List.filter_map (List.concat_map atomic_requires ~f:conjuncts) ~f:(fun t ->
      match spine t [] with
      | { term_desc = Tvar q; _ }, args ->
          let key = logical_key (scope_env ctx) q in
          let v = key in
          begin match
            (List.Assoc.find ctx.shared.views v ~equal:String.equal, List.last args)
          with
          | Some field, Some { term_desc = Tvar (Qid { pid_str = x; _ }); _ } ->
              Some (x, v, field)
          | _ -> None
          end
      | _ -> None)

(** [t] without the applications of predicates in its conjunctions. *)
let rec without_predicates ctx (t : S.term) : S.term =
  match spine (S.chain t) [] with
  | ({ term_desc = Tvar (Qid { pid_str = "&&" | "/\\"; _ }); _ } as op), [ a; b ] ->
      let a = without_predicates ctx a and b = without_predicates ctx b in
      S.mk_term (Tapply (S.mk_term (Tapply (op, a)) t.term_loc, b)) t.term_loc
  | { term_desc = Tvar q; _ }, _
    when List.Assoc.mem ctx.preds (logical_key (scope_env ctx) q) ~equal:String.equal
         || String.equal (qualid_key q) "own" ->
      S.mk_term Ttrue t.term_loc
  | _ -> t

(** The members of the pending field [p] of [st], whose calls of [helped], the procedure
    [helped_proc], wait: the ghost fields of a registration, the predicate holding its
    call's update until the call retires, committed with the result once helped, and the
    lemma helping the registrations waiting on a key. *)
let pending_members ctx (st : structure) (p : pending) (helped : func) ~helped_proc =
  let at = st.at in
  let l = loc at in
  let n x = R.Name.make ~loc:l x in
  let var x = R.Expr.var ~loc:l (n x) in
  let bin op a b = R.Expr.binary ~loc:l op a b in
  let field e f = R.Expr.field ~loc:l e (qualified_name ~loc:l (pending_name st p f)) in
  let half e f v = R.Expr.own ~loc:l [ field e f; v; R.Expr.real ~loc:l 0.5 ] in
  let decl ?(ghost = false) x t = R.Var.make ~loc:l ~ghost (ident ~loc:l x) t in
  let* key_typ = typ ctx ~at p.key_type in
  let token_typ = R.Type.atomic_token ~loc:l (qualified_name ~loc:l helped_proc) in
  let bool_typ = R.Type.bool ~loc:l and ref_typ = R.Type.ref ~loc:l in
  let* params =
    all st.params ~f:(fun (x, t) ->
        let* typ = typ ctx ~at t in
        Ok (x, t, decl x typ))
  in
  let args = List.map params ~f:(fun (x, _, _) -> var x) in
  let* () =
    if List.length helped.params = List.length params then Ok ()
    else
      unsupported helped.loc
        "Helping a function whose parameters are not those of the structure's invariant"
  in
  let* result_name, arg_names =
    contract_names helped
      (Option.bind helped.contract ~f:(fun c -> c.header))
      (List.length helped.params)
  in
  let env =
    {
      ctx;
      var_types = List.map params ~f:(fun (x, t, _) -> (x, t));
      logical_definition = false;
      data = ctx.types;
      funcs = ctx.spec_funcs;
      vars = List.map params ~f:(fun (x, _, _) -> (x, Raven x));
    }
  in
  let _, _, result = p.helping in
  let* result = formula env result in
  let registration = pending_name st p "registration" in
  let registered hc =
    R.Expr.call ~loc:l (qualified_name ~loc:l registration) (hc :: args)
  in
  let fields =
    [
      ("watched", key_typ);
      ("linked", bool_typ);
      ("token", token_typ);
      ("retired", bool_typ);
    ]
  in
  let ghost_fields =
    List.map fields ~f:(fun (f, t) ->
        R.Member.field ~loc:l ~ghost:true (generated_ident ~loc:l (pending_name st p f)) t)
  in
  (* The registration of a call: its update until it retires, committed once helped. *)
  let hc = var "hc" in
  let registration_pred =
    R.Callable.func ~loc:l ~kind:Pred
      ~formals:(decl "hc" ref_typ :: List.map params ~f:(fun (_, _, d) -> d))
      (generated_ident ~loc:l registration)
      (Some
         (R.Expr.exists ~loc:l
            [ decl "tok" token_typ; decl "l" bool_typ; decl "r" bool_typ ]
            (List.reduce_exn ~f:(bin And)
               [
                 half hc "token" (var "tok");
                 half hc "linked" (var "l");
                 half hc "retired" (var "r");
                 R.Expr.ite ~loc:l (var "r") (R.Expr.bool ~loc:l true)
                   (R.Expr.ite ~loc:l (var "l")
                      (R.Expr.au_commit ~loc:l
                         (qualified_name ~loc:l helped_proc)
                         ((var "tok" :: args) @ [ result ]))
                      (R.Expr.au ~loc:l
                         (qualified_name ~loc:l helped_proc)
                         (var "tok" :: args)));
               ])))
  in
  (* The values of the structure's views, which the helped function's implicit
     parameters are bound to by its atomic precondition. *)
  let bindings = view_bindings ctx helped in
  let* () =
    if List.length bindings <= 1 then Ok ()
    else unsupported helped.loc "Helping a function with several implicit parameters"
  in
  let* view_values =
    all st.views ~f:(fun ((v : S.predicate), _) ->
        let v = v.pred_name.pid_str in
        let* t =
          match List.Assoc.find ctx.preds v ~equal:String.equal with
          | Some (_, types) when not (List.is_empty types) -> Ok (List.last_exn types)
          | _ -> error at (Printf.sprintf "The view %s has no value" v)
        in
        let* typ = typ ctx ~at t in
        let view_field = view_field_in ctx.shared v in
        Ok ("view_" ^ v, v, view_field, t, typ))
  in
  let anchored e =
    match anchor ctx.types st.structure_type with
    | Some (_, at) -> at ~loc:l e
    | None -> e
  in
  let structure = List.hd_exn args in
  let view_owned =
    List.map view_values ~f:(fun (x, _, view_field, _, _) ->
        R.Expr.own ~loc:l
          [
            R.Expr.field ~loc:l (anchored structure) (qualified_name ~loc:l view_field);
            var x;
            R.Expr.real ~loc:l 0.5;
          ])
  in
  (* The helped function's atomic postcondition, for the result, without its predicates. *)
  let post_env =
    List.fold view_values
      ~init:
        (List.fold2_exn arg_names params ~init:env ~f:(fun env name (x, t, _) ->
             match name with
             | Some name ->
                 { (bind env name (Raven x)) with var_types = (name, t) :: env.var_types }
             | None -> env))
      ~f:(fun env (x, v, _, t, _) ->
        match List.find bindings ~f:(fun (_, w, _) -> String.equal v w) with
        | Some (implicit, _, _) ->
            {
              (bind env implicit (Raven x)) with
              var_types = (implicit, t) :: env.var_types;
            }
        | None -> env)
  in
  let post_env =
    {
      (bind post_env result_name (Value result)) with
      var_types = (result_name, helped.body.exp_type) :: post_env.var_types;
    }
  in
  let* posts =
    all
      (Option.value_map helped.contract ~default:[] ~f:(fun c -> c.atomic_ensures))
      ~f:(fun t -> formula post_env (without_predicates ctx t))
  in
  let c = var "c" and regs = var "regs" and on = var "on" and ls = var "ls" in
  let each body =
    R.Expr.forall ~loc:l [ decl "hc" ref_typ ] (bin Impl (bin In hc regs) body)
  in
  let waits_on_c = bin Eq (R.Expr.index ~loc:l on hc) c in
  let help = pending_name st p "help" in
  let call f es = R.Stmt.call ~loc:l (R.Expr.call ~loc:l (qualified_name ~loc:l f) es) in
  let local ?init x t = R.Stmt.local ~loc:l ~ghost:true ?init ~typ:t (ident ~loc:l x) in
  (* Opening a helped call's update, with the values of its implicit parameters, and
     committing it with the result. *)
  let bound =
    List.filter view_values ~f:(fun (_, v, _, _, _) ->
        List.exists bindings ~f:(fun (_, w, _) -> String.equal v w))
  in
  let opened_values = List.map bound ~f:(fun (x, _, _, _, _) -> var (x ^ "_1")) in
  let view_uses use =
    List.map bound ~f:(fun (x, v, _, _, _) ->
        let raven, _ = List.Assoc.find_exn ctx.preds v ~equal:String.equal in
        use ~loc:l (qualified_name ~loc:l raven) (args @ [ var (x ^ "_1") ]))
  in
  let commit =
    List.concat_map bound ~f:(fun (x, _, _, _, typ) -> local (x ^ "_1") typ)
    @ [
        (match opened_values with
        | [] -> call "openAU" (var "tok" :: args)
        | _ ->
            R.Stmt.assign ~loc:l opened_values
              (R.Stmt.expr_rhs (R.Expr.call ~loc:l (n "openAU") (var "tok" :: args))));
      ]
    @ view_uses (fun ~loc p args -> R.Stmt.unfold ~loc p args)
    @ view_uses (fun ~loc p args -> R.Stmt.fold ~loc p args)
    @ [ call "commitAU" ((var "tok" :: args) @ [ result ]) ]
  in
  let body =
    [
      R.Stmt.if_ ~loc:l
        (bin Neq regs (R.Expr.set ~loc:l []))
        (local "hc" ref_typ
           ~init:(R.Stmt.expr_rhs (R.Expr.call ~loc:l (n "choose") [ regs ]))
        @ [
            call help
              (args @ [ c ]
              @ List.map view_values ~f:(fun (x, _, _, _, _) -> var x)
              @ [ R.Expr.call ~loc:l (n "--") [ regs; R.Expr.set ~loc:l [ hc ] ]; on; ls ]
              );
            R.Stmt.if_ ~loc:l waits_on_c
              (local "tok" token_typ @ local "r" bool_typ
              @ [
                  R.Stmt.unfold ~loc:l
                    ~witnesses:
                      [ (ident ~loc:l "tok", var "tok"); (ident ~loc:l "r", var "r") ]
                    (qualified_name ~loc:l registration)
                    (hc :: args);
                  R.Stmt.if_ ~loc:l (R.Expr.not_ ~loc:l (var "r")) commit [];
                  R.Stmt.assign ~loc:l
                    [ field hc "linked" ]
                    (R.Stmt.expr_rhs (R.Expr.bool ~loc:l true));
                  R.Stmt.fold ~loc:l
                    ~witnesses:
                      [
                        (ident ~loc:l "tok", var "tok");
                        (ident ~loc:l "l", R.Expr.bool ~loc:l true);
                        (ident ~loc:l "r", var "r");
                      ]
                    (qualified_name ~loc:l registration)
                    (hc :: args);
                ])
              [];
          ])
        [];
    ]
  in
  let help_lemma =
    R.Callable.proc ~loc:l ~kind:Lemma
      ~formals:
        (List.map params ~f:(fun (_, _, d) -> d)
        @ [ decl "c" key_typ ]
        @ List.map view_values ~f:(fun (x, _, _, _, typ) -> decl x typ)
        @ [
            decl "regs" (R.Type.fin_set ~loc:l ref_typ);
            decl "on" (R.Type.map ~loc:l ref_typ key_typ);
            decl "ls" (R.Type.map ~loc:l ref_typ bool_typ);
          ])
      ~requires:
        (List.map (posts @ view_owned) ~f:R.Spec.make
        @ [
            R.Spec.make
              (each
                 (List.reduce_exn ~f:(bin And)
                    [
                      half hc "linked" (R.Expr.index ~loc:l ls hc);
                      registered hc;
                      bin Impl waits_on_c (R.Expr.not_ ~loc:l (R.Expr.index ~loc:l ls hc));
                    ]));
          ])
      ~ensures:
        (List.map view_owned ~f:R.Spec.make
        @ [
            R.Spec.make
              (each
                 (bin And
                    (half hc "linked" (bin Or (R.Expr.index ~loc:l ls hc) waits_on_c))
                    (registered hc)));
          ])
      ~decreases:[ regs ] (generated_ident ~loc:l help) (Some body)
  in
  Ok (ghost_fields @ [ R.Member.callable registration_pred; R.Member.callable help_lemma ])

(** The parameters of [p], with the OCaml types [param_types], and the environment of the
    predicate's body. *)
let pred_params ctx ~at (p : S.predicate) param_types =
  let l = loc at in
  let* params =
    all (List.zip_exn p.pred_params param_types) ~f:(fun ((id, _), t) ->
        let* typ = typ ctx ~at t in
        let raven = Names.fresh ctx.names id.S.pid_str in
        Ok
          (id.pid_str, raven, t, R.Var.make ~loc:(loc id.pid_loc) (ident ~loc:l raven) typ))
  in
  let env =
    {
      ctx;
      var_types = List.map params ~f:(fun (x, _, t, _) -> (x, t));
      logical_definition = false;
      data = ctx.types;
      funcs = ctx.spec_funcs;
      vars = List.map params ~f:(fun (x, raven, _, _) -> (x, Raven raven));
    }
  in
  Ok (params, env)

type checked_operation = {
  operation_binding : Module_inventory.checked_binding;
  operation_signature : Module_inventory.signature_value;
  operation_contract : S.contract option;
  operation_name : string;
  operation_member : string;
  operation_paths : Path.t list;
}

type resource_signature = {
  resource_paths : Path.t list;
  resource_declaration : S.predicate;
  resource_backend : string;
  resource_types : Types.type_expr list;
  resource_raw_types : Types.type_expr list;
}

type checked_view = {
  view_binding : Module_inventory.checked_binding;
  view_key : string;
  view_resources : (Module_inventory.signature_resource * resource_signature) list;
  view_source_substitution : Subst.t;
  view_actual_substitution : Subst.t;
  view_types : Datatypes.t list;
}

let checked_type_substitution ?(substitution = Subst.identity) binding path =
  let substitution =
    List.fold binding.Module_inventory.expected.signature_ghost_modules ~init:substitution
      ~f:(fun substitution (name, formal) ->
        let resource = formal.Module_inventory.ghost_resource in
        let owner = Subst.module_path substitution (Path.Pdot (path, name)) in
        let substitution = Subst.add_module resource.resource_id owner substitution in
        List.fold resource.resource_type_members ~init:substitution
          ~f:(fun substitution (member, id, _) ->
            Subst.add_type id (Path.Pdot (owner, String.uncapitalize member)) substitution))
  in
  List.fold binding.Module_inventory.expected.signature_types ~init:substitution
    ~f:(fun substitution (name, declaration) ->
      Subst.add_type declaration.Typedtree.typ_id
        (Subst.module_path substitution (Path.Pdot (path, name)))
        substitution)

let checked_raw_types types binding =
  let aliases =
    List.map binding.Module_inventory.expected.signature_ghost_modules
      ~f:(fun (_, formal) ->
        let resource = formal.Module_inventory.ghost_resource in
        {
          resource.resource_descriptor with
          Datatypes.alias =
            Some (Subst.type_expr binding.parameter_substitution resource.resource_type);
        })
  in
  aliases
  @ List.map types ~f:(fun data ->
      let paths =
        List.filter_map binding.Module_inventory.expected.signature_types
          ~f:(fun (name, declaration) ->
            if Datatypes.declares data (Path.Pdot (binding.actual_path, name)) then
              Some (Path.Pident declaration.Typedtree.typ_id)
            else None)
      in
      Datatypes.with_paths data paths)

let signature_contract (signature : Module_inventory.signature_value) =
  let site = signature.site in
  contract_after ~scope:site.scope site.annotations ~item_loc:site.item_loc
    ~next:site.next

type prepared_callable = {
  prepared_formals : R.Var.t list;
  prepared_args : R.Expr.t list;
  prepared_implicit : (string * string * Types.type_expr * R.Type.t * R.Loc.t) list;
  prepared_roles : (bool * bool) list;
  prepared_returns : R.Var.t list;
  prepared_requires : R.Spec.t list;
  prepared_ensures : R.Spec.t list;
}
(** The contract declaration shared by imports and checked forwarding procedures. *)

let prepare_callable ?(validate = false) ctx ~(at : Location.t) ~args ~result
    (contract : S.contract option) =
  let l = loc at in
  ctx.names.used <- Set.add ctx.names.used "r";
  let* result_typ = typ ctx ~at result in
  let header = Option.bind contract ~f:(fun c -> c.header) in
  let* result_name, names =
    match header with
    | None -> Ok ("result", List.map args ~f:(fun _ -> None))
    | Some h ->
        let* result =
          match h.hd_ret with
          | [ Lvar id ] -> Ok id.pid_str
          | [ Lwild ] | [] -> Ok "result"
          | _ -> unsupported h.hd_name.pid_loc "A contract naming several results"
        in
        let* names =
          all h.hd_args ~f:(function
            | S.Lvar id -> Ok (Some id.pid_str)
            | Lunit _ | Lwild -> Ok None
            | Lghost (id, _) ->
                unsupported id.pid_loc "A ghost parameter of a library's function")
        in
        if List.length names = List.length args then Ok (result, names)
        else
          error h.hd_name.pid_loc
            (Printf.sprintf "This contract names %d arguments, but this function has %d"
               (List.length names) (List.length args))
  in
  let* params =
    all (List.zip_exn names args) ~f:(fun (n, t) ->
        let raven = Names.fresh ctx.names (Option.value n ~default:"x") in
        let* typ = typ ctx ~at t in
        Ok (n, raven, t, R.Var.make ~loc:l (ident ~loc:l raven) typ))
  in
  let returns =
    if is_unit result then [] else [ R.Var.make ~loc:l (ident ~loc:l "r") result_typ ]
  in
  let named =
    (result_name, "r", result)
    :: List.filter_map params ~f:(fun (n, raven, t, _) ->
        Option.map n ~f:(fun n -> (n, raven, t)))
  in
  let env =
    {
      ctx;
      var_types = List.map named ~f:(fun (n, _, t) -> (n, t));
      logical_definition = false;
      data = ctx.types;
      funcs = ctx.spec_funcs;
      vars = List.map named ~f:(fun (n, raven, _) -> (n, Raven raven));
    }
  in
  let env =
    if is_unit result then bind env result_name (Value (unit_value ~loc:l)) else env
  in
  let requires = Option.value_map contract ~default:[] ~f:(fun c -> c.requires) in
  let atomic_requires =
    Option.value_map contract ~default:[] ~f:(fun c -> c.atomic_requires)
  in
  let* implicit = free_typed env (requires @ atomic_requires) ~at in
  let roles =
    List.map implicit ~f:(fun (x, _, _, _, _) ->
        ( List.exists requires ~f:(fun term ->
              List.mem (term_names term) x ~equal:String.equal),
          List.exists atomic_requires ~f:(fun term ->
              List.mem (term_names term) x ~equal:String.equal) ))
  in
  let env =
    List.fold implicit ~init:env ~f:(fun env (n, raven, t, _, _) ->
        { (bind env n (Raven raven)) with var_types = (n, t) :: env.var_types })
  in
  let* () =
    if not validate then Ok ()
    else
      let predicates q =
        Option.map
          (List.Assoc.find ctx.preds (logical_key env q) ~equal:String.equal)
          ~f:snd
      in
      let clauses =
        Option.value_map contract ~default:[] ~f:(fun c ->
            c.requires @ c.ensures @ c.atomic_requires @ c.atomic_ensures)
      in
      Signature_contract.terms ~expected:Predef.type_bool ~logical_types:ctx.types
        ~predicates ~environment:ctx.env ~variables:env.var_types clauses
  in
  let clauses ?atomic terms =
    all terms ~f:(fun t -> Result.map (formula env t) ~f:(fun e -> R.Spec.make ?atomic e))
  in
  let* requires = clauses requires in
  let* atomic_requires = clauses ~atomic:true atomic_requires in
  let* ensures =
    contract_postconditions env ~at
      (Option.value_map contract ~default:[] ~f:(fun c -> c.ensures))
  in
  let* atomic_ensures =
    contract_postconditions env ~at ~atomic:true
      (Option.value_map contract ~default:[] ~f:(fun c -> c.atomic_ensures))
  in
  let in_range =
    List.filter_map params ~f:(fun (_, raven, typ, _) -> range_spec ~loc:l typ raven)
  in
  let result_in_range = Option.to_list (range_spec ~loc:l result "r") in
  Ok
    {
      prepared_formals =
        List.map params ~f:(fun (_, _, _, v) -> v)
        @ List.map implicit ~f:(fun (_, raven, _, typ, _) ->
            R.Var.make ~loc:l ~ghost:true ~implicit:true (ident ~loc:l raven) typ);
      prepared_args =
        List.map params ~f:(fun (_, raven, _, _) -> R.Expr.var ~loc:l (name ~loc:l raven));
      prepared_implicit = implicit;
      prepared_roles = roles;
      prepared_returns = returns;
      prepared_requires = in_range @ requires @ atomic_requires;
      prepared_ensures = result_in_range @ ensures @ atomic_ensures;
    }

let prepared_member ~at ~name body prepared =
  R.Callable.proc ~loc:(loc at) ~formals:prepared.prepared_formals
    ~returns:prepared.prepared_returns ~requires:prepared.prepared_requires
    ~ensures:prepared.prepared_ensures
    (ident ~loc:(loc at) name)
    body

(** A checked call with direct argument and result forwarding. *)
let forwarding_body ctx ~at ~self ~target ~result ~atomic prepared =
  let l = loc at in
  let var x = R.Expr.var ~loc:l (name ~loc:l x) in
  let opened =
    if not atomic then []
    else
      List.map prepared.prepared_implicit ~f:(fun (_, _, _, typ, _) ->
          let x = Names.fresh ctx.names "opened" in
          (R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x), var x))
  in
  let implicit_args =
    if atomic then List.map opened ~f:snd
    else List.map prepared.prepared_implicit ~f:(fun (_, x, _, _, _) -> var x)
  in
  let call =
    R.Expr.call ~loc:l
      (qualified_name ~loc:l target)
      (prepared.prepared_args @ implicit_args)
  in
  let call_statement =
    if is_unit result then R.Stmt.call ~loc:l call
    else R.Stmt.assign ~loc:l [ var "r" ] (R.Stmt.expr_rhs call)
  in
  if not atomic then [ call_statement ]
  else
    let token = Names.fresh ctx.names "token" in
    let bind =
      R.Stmt.local ~loc:l ~ghost:true
        ~typ:(R.Type.atomic_token ~loc:l (qualified_name ~loc:l self))
        ~init:(R.Stmt.expr_rhs (R.Expr.call ~loc:l (name ~loc:l "bindAU") []))
        (ident ~loc:l token)
    in
    let open_call = R.Expr.call ~loc:l (name ~loc:l "openAU") [ var token ] in
    let opening =
      match opened with
      | [] -> R.Stmt.call ~loc:l open_call
      | _ -> R.Stmt.assign ~loc:l (List.map opened ~f:snd) (R.Stmt.expr_rhs open_call)
    in
    let commit =
      R.Stmt.call ~loc:l
        (R.Expr.call ~loc:l (name ~loc:l "commitAU")
           [ var token; (if is_unit result then unit_value ~loc:l else var "r") ])
    in
    bind @ List.concat_map opened ~f:fst @ [ opening; call_statement; commit ]

let contains_atomic_token types typ =
  let rec contains seen typ =
    match Datatypes.desc types typ with
    | Tconstr (path, args, _) ->
        List.exists args ~f:(contains seen)
        || (not (List.mem seen path ~equal:Path.same))
           && Option.exists (Datatypes.find types path) ~f:(fun data ->
               Option.is_some data.atomic_procedure
               || List.exists data.ctors ~f:(fun constructor ->
                   List.exists constructor.args ~f:(contains (path :: seen))))
    | Ttuple components -> List.exists components ~f:(fun (_, t) -> contains seen t)
    | _ -> false
  in
  contains [] typ

(** An assumed library value or procedure, using the shared contract preparation. *)
let library_function ctx ~(at : Location.t) ~name ~args ~result contract =
  match (args, contract) with
  | [], None ->
      let* result = typ ctx ~at result in
      Ok
        (R.Callable.func ~loc:(loc at)
           ~returns:[ R.Var.make ~loc:(loc at) (ident ~loc:(loc at) "r") result ]
           (ident ~loc:(loc at) name)
           None)
  | [], Some _ -> unsupported at "A contract of a library's value other than a function"
  | _ ->
      let* prepared = prepare_callable ctx ~at ~args ~result contract in
      Ok (prepared_member ~at ~name None prepared)

(** The lemmas checking that the actions of [st] keep its history's order: that each makes
    no field marked [@grows] shrink. The action's parameters have the types that its
    step's arguments give them; an action whose parameters are not all typed so is not
    checked. *)
let action_checks ctx (st : structure) =
  if not (has_history st) then Ok []
  else
    all st.actions ~f:(fun a ->
        let at = a.action_at in
        let l = loc at in
        let var x = R.Expr.var ~loc:l (name ~loc:l x) in
        let fresh x = Names.fresh ctx.names x in
        let fields =
          List.map st.fields ~f:(fun (f, _, typ, t, _) -> (f, fresh f, typ, t))
        in
        let indices =
          List.map st.chains ~f:(fun (field, _) ->
              (field, fresh (field ^ "_index"), chain_index_type ctx.types st field))
        in
        let* params =
          all st.params ~f:(fun (x, t) ->
              let* typ = typ ctx ~at t in
              Ok (x, fresh x, t, typ))
        in
        let args = List.map params ~f:(fun (_, raven, _, _) -> var raven) in
        let env =
          let env =
            bind (scope_env ctx) st.state
              (State (List.map fields ~f:(fun (f, raven, _, t) -> (f, (var raven, t)))))
          in
          List.fold params ~init:env ~f:(fun env (x, raven, t, _) ->
              { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
        in
        (* The types of the parameters, from the step's arguments. *)
        let rec typed (pattern : S.term) (t : Types.type_expr) =
          match spine (S.chain pattern) [] with
          | { term_desc = Tvar (Qid { pid_str = x; _ }); _ }, []
            when List.mem a.params x ~equal:String.equal ->
              [ (x, t) ]
          | ( { term_desc = Tvar (Qid { pid_str = "([])"; _ }); _ },
              [ _; { term_desc = Tvar (Qid { pid_str = k; _ }); _ } ] )
            when List.mem a.params k ~equal:String.equal ->
              [ (k, Predef.type_int) ]
          | { term_desc = Tvar (Qid { pid_str = c; _ }); _ }, ctor_args
            when Char.is_uppercase c.[0] -> begin
              let ctor_args =
                match ctor_args with
                | [ { term_desc = Ttuple ts; _ } ] -> ts
                | _ -> ctor_args
              in
              match find_constructor env (S.Qid (S.mk_id ~loc:pattern.term_loc c)) with
              | Some (_, ctor) when List.length ctor.args = List.length ctor_args ->
                  List.concat (List.map2_exn ctor_args ctor.args ~f:typed)
              | _ -> []
            end
          | _ -> []
        in
        let param_types =
          match a.step with
          | Some (_, Some location :: patterns) ->
              begin match
                Option.map (term_type env location) ~f:(Datatypes.desc ctx.types)
              with
              | Some (Tconstr (p, [ contents ], _)) when Datatypes.is_atomic p ->
                  List.concat_map patterns ~f:(function
                    | Some pattern -> typed pattern contents
                    | None -> [])
              | _ -> []
              end
          | _ -> []
        in
        match
          Option.all
            (List.map a.params ~f:(fun x ->
                 Option.map (List.Assoc.find param_types x ~equal:String.equal)
                   ~f:(fun t -> (x, fresh x, t))))
        with
        | None -> Ok []
        | Some action_params ->
            let* action_vars =
              all action_params ~f:(fun (_, raven, t) ->
                  let* typ = typ ctx ~at t in
                  Ok (R.Var.make ~loc:l (ident ~loc:l raven) typ))
            in
            let opened =
              {
                values = List.map fields ~f:(fun (_, raven, _, _) -> var raven);
                indices =
                  List.map indices ~f:(fun (field, raven, _) -> (field, var raven));
              }
            in
            let performing =
              {
                performed = a;
                bindings = List.map action_params ~f:(fun (x, raven, _) -> (x, var raven));
              }
            in
            let next, _, _ =
              next_state ctx st ~inv_params:st.params args opened performing
            in
            let state values = state_of ~loc:l st (grown st values) in
            (* Reported at the return point of the lemma, at the end of the action's
               name. *)
            ctx.origins :=
              {
                at = { at with loc_start = at.loc_end };
                code = Postcondition;
                message =
                  Printf.sprintf "The action %s may make a field marked [@grows] shrink"
                    a.action;
                related = [];
              }
              :: !(ctx.origins);
            Ok
              [
                R.Member.callable
                  (R.Callable.proc ~loc:l ~kind:Lemma
                     ~formals:
                       (List.map params ~f:(fun (_, raven, _, typ) ->
                            R.Var.make ~loc:l (ident ~loc:l raven) typ)
                       @ List.map fields ~f:(fun (_, raven, typ, _) ->
                           R.Var.make ~loc:l (ident ~loc:l raven) typ)
                       @ List.map indices ~f:(fun (_, raven, typ) ->
                           R.Var.make ~loc:l (ident ~loc:l raven) typ)
                       @ action_vars)
                     ~ensures:
                       [
                         R.Spec.make
                           (R.Expr.call ~loc:l
                              (qualified_name ~loc:l (member_name st "extends"))
                              [ state opened.values; state (List.map next ~f:fst) ]);
                       ]
                     (generated_ident ~loc:l (member_name st (a.action ^ "_grows")))
                     (Some []));
              ])
    |> Result.map ~f:List.concat

(** The context translating the specifications of declarations, outside functions. *)
let spec_context types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
    ?(proof_support = empty_proof_support) origins =
  {
    types;
    refs;
    primitives;
    primitive_namespace = [];
    names = Names.create ();
    functions = Path_bindings.empty;
    lifted = [];
    pasts = [];
    past_returns = [];
    origins;
    annotations = [];
    spec_funcs;
    proof_lemmas = [];
    proof_support;
    predicate_bodies = [];
    env = ocaml_env;
    preds;
    facts = [];
    au = None;
    current_procedure = None;
    manual = false;
    access_proofs = [];
    return_proofs = [];
    procedure_signatures = [];
    ghost_returns = [];
    proof_state = None;
    return_covered = false;
    initializations = [];
    linearizations = [];
    shared;
    invariants = [];
    opened = [];
    snapshots = [];
    positions = [];
    formals = [];
    ghost_args = [];
    fields_of = [];
    libraries = Path_bindings.empty;
  }

(** Recursive proof calls need checked well-founded descent, including mutual calls. *)
let check_lemma_recursion ?(resolve = fun _ q -> qualid_key q) declarations =
  let rec calls at bound (body : S.proof_expr) =
    match body.proof_desc with
    | Proof_value t ->
        let head, _ = spine t [] in
        begin match head.term_desc with
        | Tvar (Qid id) when List.mem bound id.pid_str ~equal:String.equal -> []
        | Tvar q -> [ resolve at q ]
        | _ -> []
        end
    | Proof_let (pattern, rhs, body) ->
        calls at bound rhs @ calls at (pat_names pattern @ bound) body
    | Proof_seq (rhs, body) -> calls at bound rhs @ calls at bound body
    | Proof_if (_, yes, no) -> calls at bound yes @ calls at bound no
    | Proof_match (_, cases) ->
        List.concat_map cases ~f:(fun (pattern, body) ->
            calls at (pat_names pattern @ bound) body)
    | Proof_fold _ | Proof_unfold _ | Proof_assert _ -> []
  in
  let graph =
    List.filter_map declarations ~f:(function
      | S.Proof_lemma { lemma_name; lemma_params; lemma_body; _ } ->
          Some
            ( lemma_name.pid_str,
              calls lemma_name.pid_loc
                (List.map lemma_params ~f:(fun (id, _) -> id.S.pid_str))
                lemma_body )
      | _ -> None)
  in
  let cyclic start =
    let rec visit seen = function
      | [] -> false
      | x :: pending when String.equal x start -> true
      | x :: pending when List.mem seen x ~equal:String.equal -> visit seen pending
      | x :: pending ->
          let next =
            Option.value (List.Assoc.find graph x ~equal:String.equal) ~default:[]
          in
          visit (x :: seen) (next @ pending)
    in
    visit [] (Option.value (List.Assoc.find graph start ~equal:String.equal) ~default:[])
  in
  Result.all_unit
    (List.map declarations ~f:(function
      | S.Proof_lemma { lemma_name; lemma_variant = []; _ } when cyclic lemma_name.pid_str
        ->
          error lemma_name.pid_loc "A recursive lemma needs a variant"
      | _ -> Ok ()))

(** Checked proof declarations share logical types, but introduce no runtime code. *)
let proof_lemma types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
    ~proof_lemmas ~proof_support ~predicate_bodies ?member_name origins declaration =
  match declaration with
  | S.Proof_lemma
      {
        lemma_name;
        lemma_params;
        lemma_returns;
        lemma_requires;
        lemma_ensures;
        lemma_variant;
        lemma_body;
      } ->
      let ctx =
        {
          (spec_context types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
             origins)
          with
          proof_lemmas;
          proof_support;
          predicate_bodies;
        }
      in
      let l = loc lemma_name.pid_loc in
      let signature =
        List.Assoc.find_exn proof_lemmas lemma_name.pid_str ~equal:String.equal
      in
      let declare ?(implicit = false) (id, _) ty =
        let* raven_type = typ ctx ~at:id.S.pid_loc ty in
        let raven = Names.fresh ctx.names id.pid_str in
        Ok
          ( id.pid_str,
            raven,
            ty,
            R.Var.make ~loc:(loc id.pid_loc) ~ghost:true ~implicit (ident ~loc:l raven)
              raven_type )
      in
      let* inputs =
        all (List.zip_exn lemma_params signature.lemma_inputs) ~f:(fun (parameter, ty) ->
            declare
              ~implicit:
                (List.mem (fst parameter).S.pid_attrs "implicit" ~equal:String.equal)
              parameter ty)
      in
      let* outputs =
        all (List.zip_exn lemma_returns signature.lemma_outputs)
          ~f:(fun (parameter, ty) -> declare parameter ty)
      in
      let parameters = inputs @ outputs in
      let* () =
        match
          List.find_a_dup
            (List.map parameters ~f:(fun (x, _, _, _) -> x))
            ~compare:String.compare
        with
        | None -> Ok ()
        | Some x ->
            error lemma_name.pid_loc (Printf.sprintf "Duplicate proof variable %s" x)
      in
      let env =
        {
          ctx;
          logical_definition = false;
          data = types;
          funcs = spec_funcs;
          var_types = List.map parameters ~f:(fun (x, _, ty, _) -> (x, ty));
          vars = List.map parameters ~f:(fun (x, raven, _, _) -> (x, Raven raven));
        }
      in
      let specs terms =
        all terms ~f:(fun t ->
            let* value = formula env t in
            Ok (R.Spec.make value))
      in
      let* requires = specs lemma_requires in
      let* ensures = specs lemma_ensures in
      let* decreases = all lemma_variant ~f:(formula env) in
      let body_env =
        {
          env with
          vars = List.map inputs ~f:(fun (x, raven, _, _) -> (x, Raven raven));
          var_types = List.map inputs ~f:(fun (x, _, ty, _) -> (x, ty));
        }
      in
      let targets =
        List.map outputs ~f:(fun (_, raven, ty, _) ->
            { target_name = raven; target_type = ty })
      in
      let* body = proof_expression body_env targets lemma_body in
      Ok
        (R.Callable.proc ~loc:l ~kind:Lemma
           ~formals:(List.map inputs ~f:(fun (_, _, _, v) -> v))
           ~returns:(List.map outputs ~f:(fun (_, _, _, v) -> v))
           ~requires ~ensures ~decreases
           (ident ~loc:l (Option.value member_name ~default:lemma_name.pid_str))
           (Some body))
  | _ -> error Location.none "Expected a lemma declaration"

(** The predicate [p], declared at [at], whose parameters have the OCaml types
    [param_types], defined as [def]. Each stateful invariant holds half of its views. *)
let predicate types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs ~proof_support
    ?declaration_name origins ~at ~structures (p : S.predicate) (def : definition)
    param_types : (R.Callable.t, error) Result.t =
  let ctx =
    spec_context types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
      ~proof_support origins
  in
  let l = loc at in
  let* params, env = pred_params ctx ~at p param_types in
  let vars = List.map ~f:(fun (_, _, _, v) -> v) in
  let name = ident ~loc:l (Option.value declaration_name ~default:p.pred_name.pid_str) in
  match def with
  | Direct_invariant body ->
      let* body = quantified env body in
      Ok (R.Callable.func ~loc:l ~kind:Inv ~formals:(vars params) name (Some body))
  | Body body ->
      let* body = quantified env body in
      (* Explicit output attributes override the trailing reference-free convention. *)
      let* outputs = predicate_output_count types p param_types in
      let inputs, outputs = List.split_n params (List.length params - outputs) in
      Ok
        (R.Callable.func ~loc:l ~kind:Pred ~formals:(vars inputs) ~returns:(vars outputs)
           name (Some body))
  | View _ ->
      (* Half of the view's ghost field, on the structure, its first parameter. *)
      let inputs, value = List.split_n params (List.length params - 1) in
      let structure, _, structure_type, _ = List.hd_exn params in
      let* structure =
        formula env (S.mk_term (Tvar (Qid (S.mk_id ~loc:at structure))) at)
      in
      let structure =
        match anchor types structure_type with
        | Some (_, at) -> at ~loc:l structure
        | None -> structure
      in
      let _, raven, _, _ = List.hd_exn value in
      let field =
        R.Expr.field ~loc:l structure
          (qualified_name ~loc:l (view_field_in ctx.shared p.pred_name.pid_str))
      in
      Ok
        (R.Callable.func ~loc:l ~kind:Pred ~formals:(vars inputs) ~returns:(vars value)
           name
           (Some
              (R.Expr.own ~loc:l
                 [
                   field;
                   R.Expr.var ~loc:l (R.Name.make ~loc:l raven);
                   R.Expr.real ~loc:l 0.5;
                 ])))
  | Invariant { state; body; _ } ->
      (* The state's fields are existentials, as are the index maps of the fields owned by
         index; its views hold the other halves of their ghost fields, and its history
         the authority over the states it extends. *)
      let* st =
        match
          List.find structures ~f:(fun st ->
              String.equal st.invariant p.pred_name.pid_str)
        with
        | Some st -> Ok st
        | None -> error at "An invariant without a state"
      in
      let views = st.views in
      let var x = R.Expr.var ~loc:l (R.Name.make ~loc:l x) in
      let state_env =
        bind env state
          (State (List.map st.fields ~f:(fun (f, raven, _, t, _) -> (f, (var raven, t)))))
      in
      let length s =
        R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ "Seq" ] "length") [ s ]
      in
      let bin op a b = R.Expr.binary ~loc:l op a b in
      (* Ownership of a field's entries by index, as ownership by entry, with the entries'
         positions in a map, which makes them distinct. *)
      let chain (i, guard, field, value) =
        let raven, otyp =
          match List.find st.fields ~f:(fun (f, _, _, _, _) -> String.equal f field) with
          | Some (_, raven, _, t, _) -> (raven, t)
          | None -> (field, Predef.type_int)
        in
        let index = var (List.Assoc.find_exn st.chains field ~equal:String.equal) in
        let entries = var raven in
        let* elt, elt_typ =
          match Datatypes.desc types otyp with
          | Tconstr (_, [ elt ], _) ->
              let* elt_typ = typ ctx ~at elt in
              Ok (elt, elt_typ)
          | _ -> error at "A sequence owned by index"
        in
        let j = Names.fresh ctx.names "i" and c = Names.fresh ctx.names "c" in
        let wf =
          R.Expr.forall ~loc:l
            ~triggers:[ [ R.Expr.index ~loc:l entries (var j) ] ]
            [ R.Var.make ~loc:l (ident ~loc:l j) (R.Type.int ~loc:l) ]
            (bin Impl
               (bin And
                  (bin Leq (R.Expr.int ~loc:l 0) (var j))
                  (bin Lt (var j) (length entries)))
               (bin Eq
                  (R.Expr.index ~loc:l index (R.Expr.index ~loc:l entries (var j)))
                  (var j)))
        in
        let position = R.Expr.index ~loc:l index (var c) in
        let entry_env =
          {
            (bind state_env i.S.pid_str (Value position)) with
            var_types = (i.pid_str, Predef.type_int) :: state_env.var_types;
          }
        in
        let* guard = formula entry_env guard in
        let* contents =
          match Datatypes.desc types elt with
          | Tconstr (_, [ contents ], _) -> Ok (Some contents)
          | _ -> Ok None
        in
        let* value = expected_formula entry_env contents value in
        let* field = field_of_type ctx ~at elt "" in
        let* field =
          match field with
          | Some f -> Ok f
          | None -> error at "Entries owned by index are atomics"
        in
        let owned =
          (* No trigger: one on the index map loops with the positions' trigger, through
             the next entry that an entry's value names. *)
          R.Expr.forall ~loc:l
            [ R.Var.make ~loc:l (ident ~loc:l c) elt_typ ]
            (bin Impl
               (bin And
                  (bin And
                     (bin And
                        (bin Leq (R.Expr.int ~loc:l 0) position)
                        (bin Lt position (length entries)))
                     (bin Eq (R.Expr.index ~loc:l entries position) (var c)))
                  guard)
               (R.Expr.own ~loc:l
                  [ R.Expr.field ~loc:l (var c) (qualified_name ~loc:l field); value ]))
        in
        Ok (bin And wf owned)
      in
      let* body =
        all (conjuncts body) ~f:(fun t ->
            match chain_of ~state t with
            | Some ((_, _, field, _) as owned)
              when List.Assoc.mem st.chains field ~equal:String.equal ->
                chain owned
            | _ -> quantified state_env t)
      in
      (* The registered calls, each waiting on a key, helped once the key is not the one
         that the helping action helps any more, and their registrations. *)
      let* waiting =
        all st.pendings ~f:(fun p ->
            let registrations = var (st.state ^ "_" ^ p.pending_field) in
            let on = var p.pending_on in
            let hc = R.Expr.var ~loc:l (R.Name.make ~loc:l "hc") in
            let key = R.Expr.index ~loc:l on hc in
            let helping_state, helping_key, _ = p.helping in
            let* helped_key =
              formula
                (bind state_env helping_state
                   (Option.value_exn
                      (List.Assoc.find state_env.vars state ~equal:String.equal)))
                helping_key
            in
            let pending_field f =
              R.Expr.field ~loc:l hc (qualified_name ~loc:l (pending_name st p f))
            in
            let half f v =
              R.Expr.own ~loc:l [ pending_field f; v; R.Expr.real ~loc:l 0.5 ]
            in
            (* A key that is an entry of a field owned by index is at its position. *)
            let membership =
              List.filter_map st.chains ~f:(fun (field, _) ->
                  match
                    List.find st.fields ~f:(fun (f, _, _, _, _) -> String.equal f field)
                  with
                  | Some (_, entries, _, t, _) ->
                      begin match Datatypes.desc types t with
                      | Tconstr (_, [ elt ], _)
                        when String.equal (Datatypes.tag types elt)
                               (Datatypes.tag types p.key_type) ->
                          let index =
                            R.Expr.index ~loc:l
                              (var
                                 (List.Assoc.find_exn st.chains field ~equal:String.equal))
                              key
                          in
                          Some
                            (List.reduce_exn ~f:(bin And)
                               [
                                 bin Leq (R.Expr.int ~loc:l 0) index;
                                 bin Lt index (length (var entries));
                                 bin Eq (R.Expr.index ~loc:l (var entries) index) key;
                               ])
                      | _ -> None
                      end
                  | None -> None)
            in
            let registered =
              R.Expr.call ~loc:l
                (qualified_name ~loc:l (pending_name st p "registration"))
                (hc :: List.map params ~f:(fun (_, raven, _, _) -> var raven))
            in
            Ok
              (R.Expr.forall ~loc:l
                 [ R.Var.make ~loc:l (ident ~loc:l "hc") (R.Type.ref ~loc:l) ]
                 (bin Impl (bin In hc registrations)
                    (List.reduce_exn ~f:(bin And)
                       ((half "watched" key :: membership)
                       @ [ half "linked" (bin Neq key helped_key); registered ])))))
      in
      let body = List.reduce_exn (body @ waiting) ~f:(bin And) in
      let _, structure, _, _ = List.hd_exn params in
      let anchored e =
        match anchor types st.structure_type with
        | Some (_, at) -> at ~loc:l e
        | None -> e
      in
      let* halves =
        all views ~f:(fun ((v : S.predicate), value) ->
            (* The view's parameters are the invariant's, but for its value. *)
            let view_env =
              List.fold
                (List.zip_exn (List.drop_last_exn v.pred_params) params)
                ~init:state_env
                ~f:(fun env ((id, _), (_, raven, t, _)) ->
                  {
                    (bind env id.S.pid_str (Raven raven)) with
                    var_types = (id.pid_str, t) :: env.var_types;
                  })
            in
            let* value = formula view_env value in
            let field =
              R.Expr.field ~loc:l
                (anchored (var structure))
                (qualified_name ~loc:l (view_field_in ctx.shared v.pred_name.pid_str))
            in
            Ok (R.Expr.own ~loc:l [ field; value; R.Expr.real ~loc:l 0.5 ]))
      in
      let history =
        if has_history st then
          let qn m x = generated_module_member ~loc:l m x in
          let state_value =
            R.Expr.call ~loc:l
              (qn (module_name st "state") "state")
              (grown st (List.map st.fields ~f:(fun (_, raven, _, _, _) -> var raven)))
          in
          [
            R.Expr.own ~loc:l
              [
                R.Expr.field ~loc:l
                  (anchored (var structure))
                  (qualified_name ~loc:l (member_name st "history"));
                R.Expr.call ~loc:l
                  (qn (module_name st "history") "auth")
                  [
                    R.Expr.call ~loc:l
                      (qn (module_name st "states") "set")
                      [
                        R.Expr.call ~loc:l
                          (qualified_name ~loc:l (member_name st "states"))
                          [ state_value ];
                      ];
                  ];
              ];
          ]
        else []
      in
      let body = List.fold (halves @ history) ~init:body ~f:(bin And) in
      let* ons =
        all st.pendings ~f:(fun p ->
            let* key = typ ctx ~at p.key_type in
            Ok
              (R.Var.make ~loc:l (ident ~loc:l p.pending_on)
                 (R.Type.map ~loc:l (R.Type.ref ~loc:l) key)))
      in
      let existentials =
        List.map st.fields ~f:(fun (_, raven, typ, _, _) ->
            R.Var.make ~loc:l (ident ~loc:l raven) typ)
        @ ons
        @ List.map st.chains ~f:(fun (field, raven) ->
            let elt_typ =
              match
                List.find st.fields ~f:(fun (f, _, _, _, _) -> String.equal f field)
              with
              | Some (_, _, _, t, _) ->
                  begin match Datatypes.desc types t with
                  | Tconstr (_, [ elt ], _) -> Result.ok (typ ctx ~at elt)
                  | _ -> None
                  end
              | None -> None
            in
            R.Var.make ~loc:l (ident ~loc:l raven)
              (R.Type.map ~loc:l
                 (Option.value elt_typ ~default:(R.Type.ref ~loc:l))
                 (R.Type.int ~loc:l)))
      in
      let body =
        match existentials with [] -> body | _ -> R.Expr.exists ~loc:l existentials body
      in
      Ok (R.Callable.func ~loc:l ~kind:Inv ~formals:(vars params) name (Some body))

(** The predicates of [source], declared in its interface, its proof or its annotations,
    with where they are declared, their definitions, and their parameters' types. A
    predicate declared in the interface without a definition is defined in the proof or an
    annotation, with the same parameters; an invariant in the proof defines a persistent
    predicate, and a view an exclusive one, whose value has the type of the declaration's
    last parameter. *)
let outside_scopes scopes comments =
  List.filter comments ~f:(fun (_, at) ->
      not
        (List.exists scopes ~f:(fun scope ->
             at.Location.loc_start.pos_cnum >= scope.Location.loc_start.pos_cnum
             && at.loc_end.pos_cnum <= scope.loc_end.pos_cnum)))

let direct_source_comments (source : Source.t) =
  outside_scopes
    (List.filter_map source.typed.str_items ~f:(fun item ->
         match item.Typedtree.str_desc with
         | Tstr_module _ | Tstr_modtype _ -> Some item.str_loc
         | _ -> None))
    source.comments

let direct_interface_comments (interface : Source.interface) =
  outside_scopes
    (List.filter_map interface.signature ~f:(fun item ->
         match item.Parsetree.psig_desc with
         | Psig_module _ | Psig_modtype _ -> Some item.psig_loc
         | _ -> None))
    interface.interface_comments

let predicates ~data (source : Source.t) =
  let of_annotations ~interface comments =
    all
      (List.filter
         (Annotation.of_comments comments)
         ~f:(Annotation.predicate_declaration ~interface))
      ~f:(fun a ->
        let* p = Annotation.predicate a in
        Ok (a.loc, p))
  in
  let* declared =
    Option.value_map source.interface ~default:(Ok []) ~f:(fun i ->
        of_annotations ~interface:true (direct_interface_comments i))
  in
  let* annotated = of_annotations ~interface:false (direct_source_comments source) in
  let name (p : S.predicate) = p.pred_name.pid_str in
  let declaration x = List.find declared ~f:(fun (_, p) -> String.equal (name p) x) in
  let states =
    List.filter_map source.proof ~f:(function
      | Proof_state { state_name; state_fields } -> Some (state_name.pid_str, state_fields)
      | _ -> None)
  in
  let* proof =
    all source.proof ~f:(function
      | S.Proof_predicate p ->
          Ok (Some (p.pred_name.pid_loc, p, Option.map p.pred_body ~f:(fun b -> Body b)))
      | Proof_module _ | Proof_definition _ | Proof_state _ | Proof_action _
      | Proof_lemma _ | Proof_type _ | Proof_resource _ | Proof_field _ | Proof_function _
      | Proof_au _ ->
          Ok None
      | Proof_invariant { inv_name; inv_params; inv_state = state, state_type; inv_body }
        ->
          let params, definition =
            match state_type with
            | PTtyapp (Qid t, []) when List.Assoc.mem states t.pid_str ~equal:String.equal
              ->
                let fields = List.Assoc.find_exn states t.pid_str ~equal:String.equal in
                ( inv_params,
                  Invariant
                    {
                      state = state.pid_str;
                      fields;
                      body = inv_body;
                      field_environment = source.env;
                      field_scope = None;
                    } )
            | _ -> (inv_params @ [ (state, state_type) ], Direct_invariant inv_body)
          in
          Ok
            (Some
               ( inv_name.pid_loc,
                 {
                   S.pred_name = inv_name;
                   pred_params = params;
                   pred_body = None;
                   pred_persistent = true;
                 },
                 Some definition ))
      | Proof_view { view_name; view_params; view_value } ->
          begin match declaration view_name.pid_str with
          | Some (_, d) when List.length d.pred_params = List.length view_params + 1 ->
              let value = List.last_exn d.pred_params in
              Ok
                (Some
                   ( view_name.pid_loc,
                     {
                       S.pred_name = view_name;
                       pred_params = view_params @ [ value ];
                       pred_body = None;
                       pred_persistent = false;
                     },
                     Some (View { value = view_value }) ))
          | Some (at, _) ->
              error view_name.pid_loc
                ~related:[ (at, "Its declaration") ]
                "A view has the parameters of its declaration but the last, its value"
          | None ->
              error view_name.pid_loc
                (Printf.sprintf
                   "The view %s is not declared in the interface, which gives the type \
                    of its value"
                   view_name.pid_str)
          end)
  in
  let proof = List.filter_opt proof in
  let typed (at, (p : S.predicate), def) =
    let* types =
      all p.pred_params ~f:(fun (_, t) -> Source.ocaml_type source.env ~at t)
    in
    let* _ = predicate_output_count data p types in
    Ok (at, p, def, types)
  in
  let* declared =
    all declared ~f:(fun (at, p) ->
        typed (at, p, Option.map p.pred_body ~f:(fun b -> Body b)))
  in
  let* defined =
    all
      (List.map annotated ~f:(fun (at, p) ->
           (at, p, Option.map p.pred_body ~f:(fun b -> Body b)))
      @ proof)
      ~f:typed
  in
  let with_def =
    List.filter_map ~f:(fun (at, p, def, types) ->
        Option.map def ~f:(fun def -> (at, p, def, types)))
  in
  (* Predicates defined in the interface are defined there. *)
  let defined = with_def declared @ with_def defined in
  let definitions x =
    List.filter defined ~f:(fun (_, p, _, _) -> String.equal (name p) x)
  in
  let same_types a b =
    List.length a = List.length b
    && List.for_all2_exn a b ~f:(fun a b ->
        String.equal
          (Stdlib.Format.asprintf "%a" Printtyp.type_expr a)
          (Stdlib.Format.asprintf "%a" Printtyp.type_expr b))
  in
  let is_invariant = function
    | Direct_invariant _ | Invariant _ -> true
    | Body _ | View _ -> false
  in
  let declaration (at, (p : S.predicate), def, types) =
    match (def, definitions (name p)) with
    | Some _, _ -> Ok ()
    | None, [] ->
        error at
          (Printf.sprintf
             "The predicate %s is not defined: define it in the proof or an annotation"
             (name p))
    | None, (def_at, _, _, def_types) :: _ when not (same_types types def_types) ->
        error def_at
          ~related:[ (at, "Its declaration") ]
          (Printf.sprintf
             "The predicate %s is defined with other parameter types than it is declared \
              with"
             (name p))
    | None, (def_at, _, d, _) :: _ when Bool.(p.pred_persistent <> is_invariant d) ->
        error def_at
          ~related:[ (at, "Its declaration") ]
          (if p.pred_persistent then
             Printf.sprintf "The invariant %s must be defined as an invariant" (name p)
           else
             Printf.sprintf "The predicate %s must be defined as an ordinary predicate"
               (name p))
    | None, (def_at, definition, _, def_types) :: _ ->
        let* declared_outputs = predicate_output_count data p types in
        let* defined_outputs = predicate_output_count data definition def_types in
        if declared_outputs = defined_outputs then Ok ()
        else
          error def_at
            ~related:[ (at, "Its declaration") ]
            (Printf.sprintf
               "The predicate %s has different implicit parameters in its declaration \
                and definition"
               (name p))
  in
  let definition (at, p, _, _) =
    match definitions (name p) with
    | (first, _, _, _) :: _ :: _ when not (Poly.equal first at) ->
        error at
          ~related:[ (first, "Its first definition") ]
          (Printf.sprintf "The predicate %s is defined twice" (name p))
    | _ -> Ok ()
  in
  let* () = Result.all_unit (List.map declared ~f:declaration) in
  let* () = Result.all_unit (List.map defined ~f:definition) in
  Ok defined

(** Logical definitions cannot depend on spatial resources. *)
let pure_logical_body env (t : S.term) =
  let bound = List.map env.vars ~f:fst in
  Result.all_unit
    (List.map (term_references bound t) ~f:(fun q ->
         if
           String.equal (qualid_key q) "own"
           || List.Assoc.mem env.ctx.preds (logical_key env q) ~equal:String.equal
         then
           error (S.qualid_loc q)
             "A pure logical function cannot use ownership or predicates"
         else Ok ()))

(** Nonrecursive logical definitions are checked with the rest of the proof. *)
let proof_function types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
    ~proof_support ?member_name ~as_value origins declaration =
  match declaration with
  | S.Proof_function { function_name; function_params; function_result; function_body } ->
      let l = loc function_name.pid_loc in
      let ctx =
        spec_context types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
          ~proof_support origins
      in
      let* params =
        all function_params ~f:(fun (id, ty) ->
            let* ty = Source.ocaml_type ocaml_env ~at:id.S.pid_loc ty in
            let* raven_type = typ ctx ~at:id.pid_loc ty in
            let raven = Names.fresh ctx.names id.pid_str in
            Ok (id.pid_str, raven, ty, R.Var.make ~loc:l (ident ~loc:l raven) raven_type))
      in
      let* result_type =
        Source.ocaml_type ocaml_env ~at:function_name.pid_loc function_result
      in
      let* result_type = typ ctx ~at:function_name.pid_loc result_type in
      let env =
        {
          ctx;
          data = types;
          funcs = spec_funcs;
          logical_definition = true;
          vars = List.map params ~f:(fun (x, raven, _, _) -> (x, Raven raven));
          var_types = List.map params ~f:(fun (x, _, t, _) -> (x, t));
        }
      in
      let* () = pure_logical_body env function_body in
      let* () =
        Source.check_logical_function ocaml_env ~functions:(List.map spec_funcs ~f:fst)
          declaration
      in
      let* body = formula env function_body in
      let result = Names.fresh ctx.names "result" in
      let member =
        ident ~loc:l (Option.value member_name ~default:function_name.pid_str)
      in
      let body = R.Expr.annotated body result_type in
      if as_value then Ok (R.Member.value ~loc:l ~typ:result_type member (Some body))
      else
        Ok
          (R.Member.callable
             (R.Callable.func ~loc:l
                ~formals:(List.map params ~f:(fun (_, _, _, v) -> v))
                ~returns:[ R.Var.make ~loc:l (ident ~loc:l result) result_type ]
                member (Some body)))
  | _ -> error Location.none "Expected a logical function declaration"

let scoped_contract_context types ~refs ~primitives ~shared ~environment ~proof_support
    ~preds ~spec_funcs ~own_preds ~own_inputs origins =
  let proof_support =
    { proof_support with predicate_inputs = own_inputs @ proof_support.predicate_inputs }
  in
  spec_context types ~refs ~primitives ~shared ~ocaml_env:environment ~proof_support
    ~preds:(own_preds @ preds)
    ~spec_funcs:(List.map own_preds ~f:(fun (p, (raven, _)) -> (p, raven)) @ spec_funcs)
    origins

let check_adapter_shape ~at (contract : S.contract option) =
  match contract with
  | None -> Ok ()
  | Some c ->
      let ghost =
        Option.exists c.header ~f:(fun h ->
            List.exists (h.hd_args @ h.hd_ret) ~f:(function
              | S.Lghost _ -> true
              | _ -> false))
      in
      if ghost then
        unsupported at "Explicit ghost inputs or outputs in a checked module binding"
      else if c.pure || Option.is_some c.continues || not (List.is_empty c.variant) then
        unsupported at
          "A pure, continuation, or variant contract in a checked module binding"
      else if c.atomic && List.is_empty (c.atomic_requires @ c.atomic_ensures) then
        unsupported at "An atomic module contract without atomic clauses"
      else Ok ()

let logical_contract = function
  | None -> false
  | Some (c : S.contract) ->
      c.atomic || not (List.is_empty (c.atomic_requires @ c.atomic_ensures))

let generic_modules (source : Source.t) ~fresh ~types ~functions inventory =
  let types =
    List.concat_map source.proof_resources ~f:(fun resource ->
        List.concat_map (resource :: Option.to_list resource.Source.resource_public)
          ~f:(fun resource ->
            resource.Source.resource_descriptor :: resource.resource_aliases))
    @ types
  in
  let groups =
    Generic_modules.plan
      ~proof_layout:(Generic_proofs.has_models source)
      ~fresh inventory.Module_inventory.specializations
  in
  let annotations = Annotation.of_comments source.comments in
  let rec field_term (term : S.term) =
    match S.past_membership term with
    | Some (element, _, _) -> field_term element
    | None ->
        begin match term.term_desc with
        | Tfield _ -> true
        | Tapply (a, b) | Tinfix (a, _, b) | Tlet (_, a, b) ->
            field_term a || field_term b
        | Tif (a, b, c) -> field_term a || field_term b || field_term c
        | Tquant (_, _, t) | Tcomprehension (_, t) | Tattr (_, t) | Tcast (t, _) | Told t
          ->
            field_term t
        | Tmatch (t, cases) ->
            field_term t || List.exists cases ~f:(fun (_, t) -> field_term t)
        | Ttuple ts -> List.exists ts ~f:field_term
        | Ttrue | Tfalse | Tconst _ | Tvar _ -> false
        end
  in
  let field_contract = function
    | None -> false
    | Some c ->
        List.exists
          (c.S.requires @ c.ensures @ c.atomic_requires @ c.atomic_ensures)
          ~f:field_term
  in
  let* groups =
    all groups ~f:(fun group ->
        let symbolic =
          List.concat_map (Generic_modules.parameter_groups group) ~f:(fun stage ->
              Generic_modules.types stage ~owner:(String.split stage.interface ~on:'.'))
          @ types
        in
        let* modes =
          all group.applications ~f:(fun application ->
              let concrete =
                checked_raw_types types application.Generic_modules.source.argument
              in
              all
                (List.zip_exn group.representative.parameters
                   application.source.parameters) ~f:(fun (representative, instance) ->
                  all
                    representative.Module_inventory.argument.expected.signature_resources
                    ~f:(fun (member, formal) ->
                      let actual =
                        List.Assoc.find_exn
                          instance.Module_inventory.argument.expected.signature_resources
                          member ~equal:String.equal
                      in
                      let parameters (resource : Module_inventory.signature_resource) =
                        let environment =
                          Source.annotation_env source
                            resource.Module_inventory.site.environment
                        in
                        all resource.declaration.pred_params ~f:(fun (id, pty) ->
                            Source.ocaml_type environment ~at:id.S.pid_loc pty)
                      in
                      let* symbolic_types = parameters formal in
                      let* concrete_types = parameters actual in
                      let* expected =
                        predicate_output_count symbolic formal.declaration symbolic_types
                      in
                      let* actual =
                        predicate_output_count concrete actual.declaration concrete_types
                      in
                      Ok (expected = actual))
                  |> Result.map ~f:(List.for_all ~f:Fn.id)))
        in
        let same_signature_sites application (function_ : func) =
          List.is_empty function_.signature_sites
          || List.exists group.representative.members ~f:(fun (name, representative_id) ->
              Option.exists
                (List.Assoc.find application.Generic_modules.source.members name
                   ~equal:String.equal)
                ~f:(Ident.same function_.id)
              && Option.exists
                   (List.find functions ~f:(fun representative ->
                        Ident.same representative.id representative_id))
                   ~f:(fun representative ->
                     List.equal
                       (fun (left : Module_inventory.signature_value)
                            (right : Module_inventory.signature_value) ->
                         Poly.equal left.declaration.val_loc right.declaration.val_loc)
                       function_.signature_sites representative.signature_sites))
        in
        let supported_functions =
          List.for_all group.applications ~f:(fun application ->
              List.for_all application.source.members ~f:(fun (_, id) ->
                  Option.exists
                    (List.find functions ~f:(fun f -> Ident.same f.id id))
                    ~f:(fun f ->
                      List.is_empty f.captured && List.is_empty f.prefix
                      && same_signature_sites application f
                      && (Option.is_some group.world || not (field_contract f.contract))
                      && Option.is_none f.role)))
        in
        let* parameter_contracts =
          all
            (List.concat_map group.representative.parameters ~f:(fun instance ->
                 instance.Module_inventory.argument.expected.signature_values))
            ~f:(fun (_, signature) -> signature_contract signature)
        in
        let body =
          match group.representative.template.mod_desc with
          | Tmod_functor (_, body) -> body.mod_loc
          | _ -> group.representative.template.mod_loc
        in
        let explicit_proofs =
          List.exists annotations ~f:(fun annotation ->
              let at = annotation.Annotation.loc in
              at.loc_start.pos_cnum >= body.loc_start.pos_cnum
              && at.loc_end.pos_cnum <= body.loc_end.pos_cnum
              &&
              match Annotation.kind annotation with
              | Contract | Manual | Scope | Initially | Initializes | Linearization ->
                  false
              | _ -> true)
        in
        let representation_stable =
          List.for_all group.applications ~f:(fun application ->
              List.for_all application.source.parameters ~f:(fun instance ->
                  let concrete =
                    checked_raw_types types instance.Module_inventory.argument
                  in
                  List.for_all instance.argument.expected.signature_types
                    ~f:(fun (_, declaration) ->
                      Option.is_some declaration.Typedtree.typ_manifest
                      ||
                      let t =
                        Btype.newgenty
                          (Tconstr (Path.Pident declaration.typ_id, [], ref Types.Mnil))
                      in
                      match Datatypes.desc concrete t with
                      | Tconstr (path, _, _) ->
                          Option.exists (Datatypes.find concrete path) ~f:(fun data ->
                              Option.is_some data.Datatypes.library)
                      | _ -> false)))
        in
        Ok
          (Option.some_if
             (supported_functions && representation_stable && (not explicit_proofs)
             && (not (List.exists parameter_contracts ~f:field_contract))
             && List.for_all (List.concat modes) ~f:Fn.id)
             group))
  in
  let groups = List.filter_opt groups in
  Ok
    (List.filter groups ~f:(fun group ->
         Option.is_none group.Generic_modules.world
         || List.for_all group.applications ~f:(fun application ->
             List.for_all inventory.specializations ~f:(fun other ->
                 (not (Path.same application.source.identity other.identity))
                 || List.exists group.applications ~f:(fun member ->
                     phys_equal member.source other)))))

let scoped_predicate (binding : Proof_bindings.binding) =
  match binding.kind with
  | Predicate (p, definition) ->
      let p = { p with S.pred_name = { p.pred_name with pid_str = binding.backend } } in
      let definition =
        match definition with
        | Plain body -> if p.pred_persistent then Direct_invariant body else Body body
        | Stateful { state; fields; body; environment; state_scope } ->
            Invariant
              {
                state;
                fields;
                body;
                field_environment = environment;
                field_scope = Some state_scope;
              }
        | View value -> View { value }
      in
      Some (p.pred_name.pid_loc, p, definition, binding.private_types)
  | Lemma _ | Function _ | Resource _ | Field _ | Atomic _ | State _ | Action _ -> None

let scoped_lemma (binding : Proof_bindings.binding) =
  match binding.kind with
  | Predicate _ | Function _ | Resource _ | Field _ | Atomic _ | State _ | Action _ ->
      None
  | Lemma (S.Proof_lemma lemma) ->
      Some
        (S.Proof_lemma
           { lemma with lemma_name = { lemma.lemma_name with pid_str = binding.backend } })
  | Lemma _ -> None

let scoped_function (binding : Proof_bindings.binding) =
  match binding.kind with
  | Function (S.Proof_function declaration) ->
      Some
        (S.Proof_function
           {
             declaration with
             function_name = { declaration.function_name with pid_str = binding.backend };
           })
  | Predicate _ | Lemma _ | Function _ | Resource _ | Field _ | Atomic _ | State _
  | Action _ ->
      None

let signature_has_refs ~types ~environment ~substitution typ =
  let rec contains seen typ =
    let fallback () = Datatypes.has_refs types (Subst.type_expr substitution typ) in
    match Types.get_desc (Ctype.expand_head environment typ) with
    | Tconstr (path, args, _) -> (
        List.exists args ~f:(contains seen)
        ||
        if List.mem seen path ~equal:Path.same then fallback ()
        else
          let seen = path :: seen in
          match (Env.find_type path environment).type_kind with
          | Type_abstract _ ->
              let logical =
                Option.exists (Datatypes.find types path) ~f:(fun descriptor ->
                    Option.is_some descriptor.collection
                    || descriptor.mathematical_integer)
              in
              ((not logical)
              && match path with Pident id when Ident.is_predef id -> false | _ -> true)
              || fallback ()
          | Type_record (fields, _) ->
              List.exists fields ~f:(fun field ->
                  Poly.equal field.Types.ld_mutable Asttypes.Mutable
                  || contains seen field.ld_type)
          | Type_variant (constructors, _) ->
              List.exists constructors ~f:(fun constructor ->
                  match constructor.Types.cd_args with
                  | Cstr_tuple args -> List.exists args ~f:(contains seen)
                  | Cstr_record fields ->
                      List.exists fields ~f:(fun field -> contains seen field.ld_type))
          | Type_open | Type_external _ -> fallback ())
    | Ttuple fields -> List.exists fields ~f:(fun (_, typ) -> contains seen typ)
    | Tpoly (typ, []) -> contains seen typ
    | _ -> fallback ()
  in
  contains [] typ

let check_scoped_resources ~types source inventory (proofs : Proof_bindings.t) =
  Result.all_unit
    (List.map inventory.Module_inventory.constraints ~f:(fun constraint_ ->
         match constraint_.owner with
         | None -> Ok ()
         | Some owner ->
             Result.all_unit
               (List.map constraint_.Module_inventory.signature.signature_resources
                  ~f:(fun (name, formal) ->
                    let* ( binding,
                           implementation_types,
                           implementation_environment,
                           check_projection ) =
                      match
                        List.find proofs.bindings ~f:(fun binding ->
                            Option.equal Path.same binding.entry.scope.owner (Some owner)
                            && String.equal binding.entry.name.pid_str name)
                      with
                      | Some binding ->
                          Ok
                            ( binding,
                              binding.private_types,
                              binding.environment,
                              Subst.identity )
                      | None ->
                          begin match
                            List.find proofs.applications ~f:(fun view ->
                                List.exists view.constraints ~f:(phys_equal constraint_)
                                && String.equal view.source.entry.name.pid_str name)
                          with
                          | Some view ->
                              Ok
                                ( view.source,
                                  view.implementation_types,
                                  view.environment,
                                  view.check_projection )
                          | None ->
                              error formal.site.item_loc
                                (Printf.sprintf
                                   "The module resource %s has no proof definition" name)
                          end
                    in
                    let* actual =
                      match binding.kind with
                      | Predicate (p, _) -> Ok p
                      | Lemma _ | Function _ | Resource _ | Field _ | Atomic _ | State _
                      | Action _ ->
                          error binding.entry.name.pid_loc
                            "A module resource must be defined as a predicate or \
                             invariant"
                    in
                    let declared = formal.declaration in
                    let* () =
                      if Option.is_none declared.pred_body then Ok ()
                      else
                        unsupported declared.pred_name.pid_loc
                          "A resource definition in a module signature"
                    in
                    let at = binding.entry.name.pid_loc in
                    let related =
                      [ (declared.pred_name.pid_loc, "Its signature declaration") ]
                    in
                    let* () =
                      if Bool.equal declared.pred_persistent actual.pred_persistent then
                        Ok ()
                      else
                        error at ~related
                          "The module resource has a different predicate or invariant \
                           kind"
                    in
                    let environment =
                      Source.annotation_env source formal.site.environment
                    in
                    let* raw =
                      all declared.pred_params ~f:(fun (id, ty) ->
                          Source.ocaml_type environment ~at:id.S.pid_loc ty)
                    in
                    let expected =
                      List.map raw ~f:(fun typ ->
                          Subst.type_expr check_projection
                            (Subst.type_expr constraint_.substitution typ))
                    in
                    let* equal =
                      Signature_contract.compiler ~at (fun () ->
                          List.length expected = List.length implementation_types
                          && Ctype.is_equal implementation_environment false expected
                               implementation_types)
                    in
                    let* () =
                      if equal then Ok ()
                      else
                        error at ~related
                          "The module resource has different parameter types"
                    in
                    let* expected_modes =
                      implicit_parameter_count ~kind:"predicate" declared.pred_params
                    in
                    let* actual_modes =
                      implicit_parameter_count ~kind:"predicate" actual.pred_params
                    in
                    let* expected_outputs =
                      Signature_contract.compiler ~at (fun () ->
                          predicate_output_count
                            ~has_refs:
                              (signature_has_refs ~types ~environment
                                 ~substitution:constraint_.substitution)
                            types declared raw)
                      |> Result.join
                    in
                    let* actual_outputs =
                      predicate_output_count types actual implementation_types
                    in
                    if
                      Poly.equal expected_modes actual_modes
                      && Int.equal expected_outputs actual_outputs
                    then Ok ()
                    else
                      error at ~related
                        "The module resource has different implicit parameter modes"))))

let program (source : Source.t) : (R.Program.t * origin list, error) Result.t =
  let annotations = Annotation.of_comments source.comments in
  (* Each annotation on an atomic step, by the end of the code it follows. *)
  let linearizations =
    List.filter_map annotations ~f:(fun a ->
        if Poly.equal (Annotation.kind a) Annotation.Linearization then
          let rec anchor i =
            if i > 0 && Char.is_whitespace source.text.[i - 1] then anchor (i - 1) else i
          in
          Some (anchor a.loc.loc_start.pos_cnum, a)
        else None)
  in
  (* Each follows an application of an [Atomic] operation. *)
  let typed = without_application_operators source.typed in
  let steps = atomic_steps typed in
  let* initializations = initialization_annotations source typed annotations in
  let* () =
    match
      List.find linearizations ~f:(fun (anchor, _) ->
          not (List.mem steps anchor ~equal:Int.equal))
    with
    | Some (_, a) ->
        error a.loc "This annotation does not follow an atomic step, as Atomic.get t"
    | None -> Ok ()
  in
  let backend_names = Names.create () in
  backend_names.used <-
    Set.of_list
      (module String)
      [
        "Library";
        "List";
        "Option";
        "Seq";
        "FinSet";
        "Set";
        "Map";
        "Int";
        "Real";
        "Bool";
        Prelude.div;
        Prelude.mod_;
        Prelude.in_range;
        Prelude.wrap;
      ];
  let reserved =
    List.map source.libraries ~f:(fun lib -> lib.Source.library_name)
    @ List.map source.proof_types ~f:(fun data -> data.Datatypes.module_name)
    @ List.concat_map source.proof_resources ~f:(fun resource ->
        List.map (resource.Source.resource_descriptor :: resource.resource_aliases)
          ~f:(fun data -> data.Datatypes.module_name))
    @ List.filter_map source.proof ~f:(function
      | S.Proof_function { function_name; _ } -> Some function_name.pid_str
      | Proof_lemma { lemma_name; _ } -> Some lemma_name.pid_str
      | Proof_predicate p -> Some p.pred_name.pid_str
      | Proof_invariant { inv_name; _ } -> Some inv_name.pid_str
      | Proof_view { view_name; _ } -> Some view_name.pid_str
      | _ -> None)
  in
  let declarations ~interface comments =
    List.filter
      (Annotation.of_comments comments)
      ~f:(Annotation.predicate_declaration ~interface)
  in
  let declarations =
    declarations ~interface:false (direct_source_comments source)
    @ Option.value_map source.interface ~default:[] ~f:(fun interface ->
        declarations ~interface:true (direct_interface_comments interface))
  in
  let* declared_predicates = all declarations ~f:Annotation.predicate in
  let reserved =
    reserved @ List.map declared_predicates ~f:(fun p -> p.S.pred_name.pid_str)
  in
  backend_names.used <-
    Set.union backend_names.used (Set.of_list (module String) reserved);
  let fresh = Names.fresh backend_names in
  let source =
    let scoped_types =
      List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
          match entry.Proof_scopes.declaration with
          | S.Proof_type _ when Option.is_some entry.scope.owner ->
              Some entry.name.pid_loc
          | _ -> None)
    in
    {
      source with
      proof_resources =
        List.map source.proof_resources ~f:(fun resource ->
            match resource.Source.resource_scope with
            | None when resource.resource_abstract ->
                let backend = fresh resource.resource_backend in
                {
                  resource with
                  resource_backend = backend;
                  resource_descriptor =
                    Datatypes.with_name resource.resource_descriptor backend;
                }
            | None -> resource
            | Some owner ->
                let namespace =
                  Option.value_map
                    (Proof_scopes.find_owner source.proof_scopes (Some owner)) ~default:[]
                    ~f:(fun scope -> scope.namespace)
                in
                let backend =
                  fresh (String.concat ~sep:"_" (namespace @ [ resource.resource_name ]))
                in
                {
                  resource with
                  resource_backend = backend;
                  resource_descriptor =
                    Datatypes.with_name resource.resource_descriptor backend;
                  resource_public =
                    Option.map resource.resource_public ~f:(fun public ->
                        let backend = fresh ("Export_" ^ backend) in
                        {
                          public with
                          resource_backend = backend;
                          resource_descriptor =
                            Datatypes.with_name public.resource_descriptor backend;
                        });
                });
      proof_fields =
        List.map source.proof_fields ~f:(fun field ->
            match field.Source.field_scope with
            | None -> field
            | Some owner ->
                let namespace =
                  Option.value_map
                    (Proof_scopes.find_owner source.proof_scopes (Some owner)) ~default:[]
                    ~f:(fun scope -> scope.namespace)
                in
                {
                  field with
                  field_backend =
                    fresh
                      (String.uncapitalize
                         (String.concat ~sep:"_" (namespace @ [ field.field_name ])));
                });
      proof_types =
        List.map source.proof_types ~f:(fun data ->
            if List.mem scoped_types data.Datatypes.at ~equal:Poly.equal then
              Datatypes.with_name data (fresh data.module_name)
            else data);
    }
  in
  let resource_implementations =
    List.filter_map source.proof_resources ~f:(fun resource ->
        Option.some_if
          (resource.Source.resource_definition
          && Option.is_none resource.resource_application)
          (resource.resource_id, fresh ("Implementation_" ^ resource.resource_backend)))
  in
  let proof_implementations =
    List.filter_map source.proof_resources ~f:(fun resource ->
        Option.some_if
          (resource.Source.resource_definition
          && Option.is_none resource.resource_application)
          (resource.resource_id, fresh ("Proofs_" ^ resource.resource_backend)))
  in
  let implementation resource =
    List.Assoc.find resource_implementations resource.Source.resource_id ~equal:Ident.same
  in
  let proof_implementation resource =
    List.Assoc.find proof_implementations resource.Source.resource_id ~equal:Ident.same
  in
  let definition_resource scope =
    Option.bind scope.Proof_scopes.owner ~f:(fun owner ->
        List.find source.proof_resources ~f:(fun resource ->
            resource.resource_definition
            && (Path.same owner resource.resource_path
               || Path.same owner (Path.Pident resource.resource_id))))
  in
  let definition_target (binding : Proof_bindings.binding) =
    Option.bind (definition_resource binding.entry.scope) ~f:(fun resource ->
        let backend =
          match binding.kind with
          | Predicate _ | Lemma _ -> proof_implementation resource
          | Function _ | Resource _ | Field _ | Atomic _ | State _ | Action _ ->
              implementation resource
        in
        Option.map backend ~f:(fun backend -> backend ^ "." ^ binding.entry.name.pid_str))
  in
  let* inventory = Module_inventory.build source typed in
  let* scoped_proofs = Proof_bindings.build ~fresh source inventory in
  let scoped_binding name =
    List.find scoped_proofs.bindings ~f:(fun binding -> String.equal binding.backend name)
  in
  let declaration_scope name =
    Option.map (scoped_binding name) ~f:(fun binding -> binding.entry.scope)
  in
  let declaration_environment name =
    Option.value_map (scoped_binding name) ~default:source.env ~f:(fun binding ->
        binding.environment)
  in
  let definition_member_name name =
    Option.bind (scoped_binding name) ~f:(fun binding ->
        Option.map (definition_target binding) ~f:(fun _ -> binding.entry.name.pid_str))
  in
  let typed = inventory.structure in
  let* libraries = Library_modules.flatten ~fresh source.libraries in

  List.iter libraries ~f:(fun lib ->
      List.iter lib.Library_modules.library.signature ~f:(fun item ->
          match item.Parsetree.psig_desc with
          | Psig_type (_, decls) ->
              List.iter decls ~f:(fun decl ->
                  backend_names.used <-
                    Set.add backend_names.used
                      (lib.library_name ^ "_" ^ decl.Parsetree.ptype_name.txt))
          | _ -> ()));
  let* types, funcs = items source ~fresh inventory in
  let* lifted = all funcs ~f:(fun f -> local_functions ~source f annotations) in
  let lifted =
    List.map (List.concat lifted) ~f:(fun f -> { f with raven_name = fresh f.raven_name })
  in
  let funcs = inherit_contracts (funcs @ lifted) in
  let* access_proofs =
    access_annotations ~libraries
      ~checked:
        (List.concat_map inventory.bindings ~f:(fun binding ->
             List.concat_map binding.Module_inventory.paths ~f:(fun path ->
                 List.map binding.expected.signature_values ~f:(fun (member, _) ->
                     Path.Pdot (path, member)))))
      source typed annotations ~functions:funcs
  in
  let state_targets = ref [] and nested_reads = ref [] in
  let remember (e : Typedtree.expression) =
    state_targets :=
      (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum) :: !state_targets
  in
  let rec lexical_tail (e : Typedtree.expression) =
    remember e;
    match e.exp_desc with
    | Texp_let (_, _, body) | Texp_sequence (_, body) -> lexical_tail body
    | Texp_ifthenelse (_, yes, no) ->
        lexical_tail yes;
        Option.iter no ~f:lexical_tail
    | Texp_match (_, cases, _, _) ->
        List.iter cases ~f:(fun c -> lexical_tail c.Typedtree.c_rhs)
    | _ -> ()
  in
  let visit iterator (e : Typedtree.expression) =
    if Option.is_some (atomic_read_argument e) then nested_reads := e :: !nested_reads;
    begin match e.exp_desc with
    | Texp_let (Nonrecursive, [ binding ], body) ->
        remember binding.vb_expr;
        lexical_tail body
    | Texp_let (_, _, body) -> lexical_tail body
    | Texp_sequence (left, right) ->
        remember left;
        lexical_tail right
    | Texp_ifthenelse (_, yes, no) ->
        lexical_tail yes;
        Option.iter no ~f:lexical_tail
    | Texp_match (_, cases, _, _) ->
        List.iter cases ~f:(fun c -> lexical_tail c.Typedtree.c_rhs)
    | Texp_while (_, body) | Texp_for (_, _, _, _, _, body) -> lexical_tail body
    | _ -> ()
    end;
    Tast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Tast_iterator.default_iterator with expr = visit } in
  List.iter funcs ~f:(fun f ->
      lexical_tail f.body;
      iterator.expr iterator f.body);
  let* () =
    Result.all_unit
      (List.map !nested_reads ~f:(fun e ->
           let* argument = nested_stateful_read access_proofs e in
           Option.iter argument ~f:(fun argument ->
               remember e;
               remember argument);
           Ok ()))
  in
  let* () =
    Result.all_unit
      (List.map access_proofs ~f:(fun (key, a) ->
           let* scope = Annotation.scope a in
           if
             Option.is_some scope.scope_state
             && not (List.mem !state_targets key ~equal:Poly.equal)
           then
             error a.loc
               "A stateful scope needs a direct let binding, sequence continuation, \
                lexical tail, or directly nested stateful read"
           else Ok ()))
  in
  let tails = ref [] in
  let rec collect_tail (e : Typedtree.expression) =
    tails := (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum) :: !tails;
    match e.exp_desc with
    | Texp_let (_, _, body) | Texp_sequence (_, body) -> collect_tail body
    | Texp_ifthenelse (_, yes, no) ->
        collect_tail yes;
        Option.iter no ~f:collect_tail
    | Texp_match (_, cases, _, _) ->
        List.iter cases ~f:(fun c -> collect_tail c.Typedtree.c_rhs)
    | _ -> ()
  in
  List.iter funcs ~f:(fun f -> collect_tail f.body);
  let* return_proofs =
    attached_annotations ~all_expressions:true ~innermost:true source typed annotations
      ~kind:Annotation.Returns
      ~is_target:(fun e ->
        List.mem !tails
          (e.Typedtree.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum)
          ~equal:Poly.equal)
      ~description:"Ghost.returns must follow a normal tail expression"
  in
  let* () =
    Result.all_unit
      (List.map (access_proofs @ return_proofs) ~f:(fun ((start, finish), annotation) ->
           let owners =
             List.filter funcs ~f:(fun f ->
                 start >= f.body.exp_loc.loc_start.pos_cnum
                 && finish <= f.body.exp_loc.loc_end.pos_cnum)
           in
           match
             List.min_elt owners ~compare:(fun a b ->
                 Int.compare
                   (a.body.exp_loc.loc_end.pos_cnum - a.body.exp_loc.loc_start.pos_cnum)
                   (b.body.exp_loc.loc_end.pos_cnum - b.body.exp_loc.loc_start.pos_cnum))
           with
           | Some f when f.manual && not f.trusted -> Ok ()
           | Some f when f.trusted ->
               error annotation.loc "Ghost.scope cannot be used in a trusted function"
           | _ -> error annotation.loc "Ghost.scope requires a manual function proof"))
  in
  (* The abstract types of the libraries. *)
  let* library_types =
    all libraries ~f:(fun (lib : Library_modules.t) ->
        all lib.library.signature ~f:(fun (item : Parsetree.signature_item) ->
            match item.psig_desc with
            | Psig_type (_, decls) ->
                all decls ~f:(fun (decl : Parsetree.type_declaration) ->
                    match (decl.ptype_kind, decl.ptype_manifest, decl.ptype_params) with
                    | Ptype_abstract, None, [] ->
                        Ok
                          ( Datatypes.library_type ~library:lib.library_name
                              ~library_id:lib.library_id ~at:decl.ptype_loc
                              decl.ptype_name.txt
                          |> fun descriptor ->
                            Datatypes.with_paths descriptor
                              [ Path.Pdot (lib.library_path, decl.ptype_name.txt) ] )
                    | _ ->
                        unsupported decl.ptype_loc
                          "A type of a library other than an abstract one without \
                           parameters")
            | _ -> Ok []))
  in
  let types = List.concat (List.concat library_types) @ types @ source.proof_types in
  let rec alias_path ~target ~alias path =
    if Path.same target path then Some alias
    else
      match path with
      | Path.Pdot (parent, name) ->
          Option.map (alias_path ~target ~alias parent) ~f:(fun parent ->
              Path.Pdot (parent, name))
      | Papply (head, argument) ->
          let head_alias = alias_path ~target ~alias head in
          let argument_alias = alias_path ~target ~alias argument in
          if Option.is_none head_alias && Option.is_none argument_alias then None
          else
            Some
              (Path.Papply
                 ( Option.value head_alias ~default:head,
                   Option.value argument_alias ~default:argument ))
      | Pident _ | Pextra_ty _ -> None
  in
  let types =
    List.map types ~f:(fun data ->
        let declared =
          data.Datatypes.paths @ Option.to_list data.library
          @ Option.to_list (Option.map data.id ~f:(fun id -> Path.Pident id))
        in
        let rec expand remaining paths =
          let aliases =
            List.concat_map inventory.aliases ~f:(fun (alias, target) ->
                List.filter_map paths ~f:(alias_path ~target ~alias))
          in
          let expanded = Datatypes.with_paths data (paths @ aliases) in
          if remaining = 0 || List.length expanded.paths = List.length paths then expanded
          else expand (remaining - 1) expanded.paths
        in
        expand (List.length inventory.aliases) declared)
  in
  let* types =
    List.fold_result inventory.bindings ~init:types ~f:(fun types binding ->
        List.fold_result binding.Module_inventory.expected.signature_types ~init:types
          ~f:(fun types (member, declaration) ->
            let actual = Path.Pdot (binding.actual_path, member) in
            match Datatypes.find types actual with
            | None ->
                unsupported declaration.Typedtree.typ_loc
                  "A checked module type without a supported representation"
            | Some descriptor ->
                let aliases =
                  List.map binding.paths ~f:(fun path -> Path.Pdot (path, member))
                in
                Ok
                  (List.map types ~f:(fun data ->
                       if phys_equal data descriptor then
                         Datatypes.with_paths data aliases
                       else data))))
  in
  let public_types =
    List.concat_map inventory.bindings ~f:(fun binding ->
        List.concat_map binding.Module_inventory.expected.signature_types
          ~f:(fun (member, _) ->
            List.map binding.paths ~f:(fun path -> Path.Pdot (path, member))))
  in
  let* generics = generic_modules source ~fresh ~types ~functions:funcs inventory in
  let* module_scopes = Module_context.collect_scopes source.proof_scopes in
  let* generic_proofs = Generic_proofs.plan generics module_scopes in
  let module_contexts = Module_context.plan ~scopes:module_scopes generic_proofs in
  let declaration_context name =
    Module_context.for_scope module_contexts (declaration_scope name)
  in
  let asset_context owner = Module_context.for_owner module_contexts owner in
  let context_for_group group =
    Option.value
      (Module_context.for_group module_contexts group)
      ~default:module_contexts.root
  in
  let* generic_proof_types =
    all generic_proofs ~f:Generic_proofs.types |> Result.map ~f:List.concat
  in
  let* _ =
    all scoped_proofs.bindings ~f:(fun binding ->
        if
          Option.is_none
            (Proof_bindings.functor_ancestor source.proof_scopes binding.entry.scope)
          || Option.is_some
               (Generic_proofs.owner generic_proofs (Some binding.entry.scope))
        then Ok ()
        else
          unsupported binding.entry.name.pid_loc
            "A functor proof without a supported generic runtime body and application")
  in
  let* _ =
    all source.proof_types ~f:(fun data ->
        match Generic_proofs.model_owner source data with
        | Some scope
          when Option.is_some (Proof_bindings.functor_ancestor source.proof_scopes scope)
               && Option.is_none (Generic_proofs.owner generic_proofs (Some scope)) ->
            unsupported data.Datatypes.at
              "A functor proof without a supported generic runtime body and application"
        | Some _ | None -> Ok ())
  in
  let proof_worker name = (declaration_context name).worker in
  let* applications =
    Generic_proofs.applications ~fresh source inventory scoped_proofs generic_proofs
  in
  let scoped_proofs = Proof_bindings.with_applications scoped_proofs applications in
  let asset_worker owner = (asset_context owner).worker in
  let source =
    let project_descriptor context backend abstract_member descriptor =
      if List.is_empty context.Module_context.namespace then descriptor
      else
        let descriptor =
          List.fold (Option.value_map abstract_member ~default:[] ~f:fst) ~init:descriptor
            ~f:(fun descriptor parameter ->
              match abstract_member with
              | Some (_, member) ->
                  Datatypes.with_paths descriptor
                    [ Path.Pdot (Path.Pdot (Path.Pident parameter, member), "t") ]
              | None -> descriptor)
        in
        {
          descriptor with
          Datatypes.module_name = backend;
          module_path = Some (String.split backend ~on:'.');
          backend_type =
            Some Qualified_name.{ path = String.split backend ~on:'.'; name = "T" };
        }
    in
    {
      source with
      proof_resources =
        List.map source.proof_resources ~f:(fun resource ->
            let context = asset_context resource.Source.resource_scope in
            let parameter =
              if resource.resource_abstract then
                List.find context.parameters ~f:(fun parameter ->
                    Option.exists parameter.Generic_proofs.original ~f:(fun original ->
                        Source.resource_has_path resource
                          (Path.Pdot (Path.Pident original, resource.resource_name))))
              else None
            in
            let backend =
              Module_context.member context
                (Option.value_map parameter ~default:resource.resource_backend
                   ~f:(fun parameter ->
                     parameter.generic.parameter ^ "." ^ resource.resource_name))
            in
            let abstract_member =
              Option.map parameter ~f:(fun parameter ->
                  ( Option.to_list parameter.original @ [ parameter.instance.parameter ],
                    resource.resource_name ))
            in
            {
              resource with
              resource_backend = backend;
              resource_descriptor =
                project_descriptor context backend abstract_member
                  resource.resource_descriptor;
              resource_aliases =
                List.map resource.resource_aliases
                  ~f:(project_descriptor context backend None);
              resource_public =
                Option.map resource.resource_public ~f:(fun public ->
                    let backend = Module_context.member context public.resource_backend in
                    {
                      public with
                      resource_backend = backend;
                      resource_descriptor =
                        project_descriptor context backend None public.resource_descriptor;
                    });
            });
      proof_fields =
        List.map source.proof_fields ~f:(fun field ->
            let context = asset_context field.Source.field_scope in
            {
              field with
              field_backend = Module_context.member context field.field_backend;
            });
    }
  in
  let resource_views resource =
    resource :: Option.to_list resource.Source.resource_public
  in
  let application_resources =
    Generic_proofs.resource_applications source inventory generic_proofs
    |> List.map ~f:(fun resource ->
        match
          List.find source.proof_resources ~f:(fun view ->
              Option.is_some view.Source.resource_application
              && Path.same view.resource_path resource.Source.resource_path)
        with
        | None -> resource
        | Some view ->
            {
              resource with
              resource_id = view.resource_id;
              resource_application = view.resource_application;
              resource_public =
                Option.map resource.resource_public ~f:(fun public ->
                    Option.value_map view.resource_public ~default:public ~f:(fun view ->
                        { public with resource_id = view.resource_id }));
            })
  in
  let all_resources =
    application_resources
    @ List.filter source.proof_resources ~f:(fun r ->
        Option.is_none r.Source.resource_application)
  in
  let all_resource_views = List.concat_map all_resources ~f:resource_views in
  let resource_binding resource =
    List.find scoped_proofs.bindings ~f:(fun binding ->
        match binding.Proof_bindings.kind with
        | Resource actual -> Ident.same actual.resource_id resource.Source.resource_id
        | _ -> false)
  in
  let resource_view ~scope resource =
    match resource_binding resource with
    | Some binding when Proof_bindings.opaque_at scoped_proofs ~scope binding ->
        Option.value resource.resource_public ~default:resource
    | None ->
        begin match
          List.find scoped_proofs.applications ~f:(fun view ->
              Path.same
                (Path.Pdot (view.Proof_bindings.path, view.source.entry.name.pid_str))
                resource.Source.resource_path)
        with
        | Some view when Proof_bindings.application_opaque scoped_proofs ~scope view ->
            Option.value resource.resource_public ~default:resource
        | Some _ | None -> resource
        end
    | Some _ -> resource
  in
  let private_ra_types =
    List.filter_map source.proof_types ~f:(fun data ->
        Option.bind (Generic_proofs.model_owner source data) ~f:(fun scope ->
            if Option.is_none scope.Proof_scopes.definition then None
            else
              Option.map (Generic_proofs.owner generic_proofs (Some scope))
                ~f:(fun plan ->
                  let backend = plan.group.name ^ "." ^ data.Datatypes.module_name in
                  ( plan,
                    {
                      data with
                      module_path = Some (String.split backend ~on:'.');
                      backend_type =
                        Some
                          Qualified_name.
                            { path = String.split backend ~on:'.'; name = "T" };
                    } ))))
  in
  let proof_assets scope =
    let environment =
      Option.value_map scope ~default:source.env ~f:(fun scope ->
          Source.annotation_env source scope.Proof_scopes.environment)
    in
    let rebase = Proof_bindings.context_type scoped_proofs ~environment in
    let private_owner owner =
      match (owner, scope) with
      | None, _ -> true
      | Some owner, Some caller ->
          Option.exists (Proof_scopes.find_owner source.proof_scopes (Some owner))
            ~f:(fun owner ->
              Option.is_some
                (Proof_bindings.drop_prefix owner.namespace caller.Proof_scopes.namespace))
      | Some _, None -> false
    in
    let project owner typ =
      if private_owner owner then typ
      else rebase (Proof_bindings.public_type scoped_proofs typ)
    in
    let visible entry =
      Option.value_map entry ~default:true
        ~f:(Proof_bindings.visible scoped_proofs ~scope)
    in
    let resources =
      List.filter_map
        (List.filter source.proof_resources ~f:(fun resource ->
             Option.is_none resource.Source.resource_application))
        ~f:(fun resource ->
          let binding =
            List.find scoped_proofs.bindings ~f:(fun binding ->
                match binding.kind with
                | Resource actual ->
                    Ident.same actual.resource_id resource.Source.resource_id
                | _ -> false)
          in
          if not (visible binding) then None
          else
            let resource = resource_view ~scope resource in
            let project = project resource.resource_scope in
            Some
              {
                resource with
                resource_type = project resource.resource_type;
                resource_operations =
                  List.map resource.resource_operations ~f:(fun (name, inputs, output) ->
                      (name, List.map inputs ~f:project, project output));
              })
    in
    let fields =
      List.filter_map source.proof_fields ~f:(fun field ->
          let binding =
            List.find scoped_proofs.bindings ~f:(fun binding ->
                match binding.kind with
                | Field actual -> Ident.same actual.field_id field.Source.field_id
                | _ -> false)
          in
          if not (visible binding) then None
          else
            let project = project field.field_scope in
            Some
              {
                field with
                field_owner = project field.field_owner;
                field_value = project field.field_value;
              })
    in
    let application_resources =
      List.filter_map application_resources ~f:(fun resource ->
          let view =
            List.find scoped_proofs.applications ~f:(fun view ->
                Path.same
                  (Path.Pdot (view.Proof_bindings.path, view.source.entry.name.pid_str))
                  resource.Source.resource_path)
          in
          match view with
          | Some view when Proof_bindings.application_visible scoped_proofs ~scope view ->
              Some
                (if Proof_bindings.application_opaque scoped_proofs ~scope view then
                   Option.value resource.resource_public ~default:resource
                 else resource)
          | Some _ | None -> None)
    in
    let application_fields =
      List.filter_map scoped_proofs.applications ~f:(fun view ->
          match view.Proof_bindings.source.kind with
          | Field original
            when Proof_bindings.application_visible scoped_proofs ~scope view ->
              Option.map
                (List.find source.proof_fields ~f:(fun field ->
                     Ident.same field.Source.field_id original.field_id))
                ~f:(fun field ->
                  let prefix = (Qualified_name.of_string view.backend).path in
                  let leaf = (Qualified_name.of_string field.field_backend).name in
                  {
                    field with
                    field_path = Path.Pdot (view.path, field.field_name);
                    field_backend = String.concat ~sep:"." (prefix @ [ leaf ]);
                    field_owner = view.project_type field.field_owner;
                    field_value = view.project_type field.field_value;
                    field_resource =
                      Option.map field.field_resource ~f:(fun owner ->
                          match
                            Types.get_desc
                              (view.project_type
                                 (Ctype.newconstr (Path.Pdot (owner, "t")) []))
                          with
                          | Tconstr (Path.Pdot (owner, "t"), [], _) -> owner
                          | _ -> owner);
                  })
          | _ -> None)
    in
    (resources @ application_resources, fields @ application_fields)
  in
  let layouts = Result_layouts.plan types generics in
  let* types = Result_layouts.concrete layouts types in
  let schema binding =
    Option.map (Generic_modules.application_for_binding generics binding)
      ~f:(fun (group, application) ->
        Checked_modules.
          {
            interface = Generic_modules.interface group application;
            members = group.operations;
          })
  in
  let checked_modules = Checked_modules.plan ~schema ~fresh inventory.bindings in
  let* checked_operations =
    all checked_modules ~f:(fun view ->
        let binding = view.Checked_modules.binding in
        all binding.Module_inventory.expected.signature_values
          ~f:(fun (member, signature) ->
            let* contract = signature_contract signature in
            let* () =
              match contract with
              | Some c when c.S.pure || Option.is_some c.continues ->
                  unsupported signature.site.item_loc
                    "A pure or continuation contract in a checked module view"
              | _ -> Ok ()
            in
            let operation_member =
              List.Assoc.find_exn view.members member ~equal:String.equal
            in
            Ok
              {
                operation_binding = binding;
                operation_signature = signature;
                operation_contract = contract;
                operation_name =
                  (if view.grouped then view.name ^ "." ^ operation_member
                   else operation_member);
                operation_member;
                operation_paths =
                  List.map binding.paths ~f:(fun path -> Path.Pdot (path, member));
              }))
  in
  let checked_operations = List.concat checked_operations in

  (* The data types, and the sequences of specifications, which have no module. *)
  let* inferred_pure = pure_functions funcs in
  let pure =
    inferred_pure
    @ List.filter funcs ~f:(fun f ->
        let inferred id =
          List.exists inferred_pure ~f:(fun pure -> Ident.same pure.id id)
        in
        (not (inferred f.id))
        && Option.exists (Generic_modules.member generics f.id)
             ~f:(fun (group, _, stem) ->
               List.exists group.applications ~f:(fun application ->
                   List.exists application.source.members ~f:(fun (source, id) ->
                       String.equal
                         (List.Assoc.find_exn group.members source ~equal:String.equal)
                         stem
                       && inferred id))))
  in
  let is_pure (f : func) = List.exists pure ~f:(fun g -> Ident.same g.id f.id) in
  let generic_procedures =
    List.concat_map generics ~f:(fun group ->
        List.map group.members ~f:(fun (source, stem) ->
            let id =
              List.Assoc.find_exn group.representative.members source ~equal:String.equal
            in
            let f = List.find_exn funcs ~f:(fun f -> Ident.same f.id id) in
            (group.name ^ "." ^ stem, if is_pure f then fresh (stem ^ "_impl") else stem)))
  in
  let procedure_stem group stem =
    List.Assoc.find_exn generic_procedures
      (group.Generic_modules.name ^ "." ^ stem)
      ~equal:String.equal
  in
  let pure_name f =
    match Generic_modules.member generics f.id with
    | None -> f.raven_name
    | Some (_, application, stem) -> application.name ^ "." ^ stem
  in
  let pure_reference f =
    match Generic_modules.member generics f.id with
    | None -> Qualified_name.{ path = []; name = f.raven_name }
    | Some _ -> Qualified_name.of_string (pure_name f)
  in
  let procedures =
    List.map funcs ~f:(fun f ->
        let name =
          match Generic_modules.member generics f.id with
          | None -> if is_pure f then fresh (f.raven_name ^ "_impl") else f.raven_name
          | Some (group, application, stem) ->
              application.name ^ "." ^ procedure_stem group stem
        in
        (f.id, name))
  in
  let proc_name (f : func) = List.Assoc.find_exn procedures f.id ~equal:Ident.same in
  let body_proc_name f =
    match Generic_modules.member generics f.id with
    | None -> proc_name f
    | Some (group, _, stem) -> group.name ^ "." ^ procedure_stem group stem
  in
  let body_pure_name f =
    match Generic_modules.member generics f.id with
    | None -> pure_name f
    | Some (group, _, stem) -> group.name ^ "." ^ stem
  in
  let body_pure_reference f =
    match Generic_modules.member generics f.id with
    | None -> pure_reference f
    | Some _ -> Qualified_name.of_string (body_pure_name f)
  in
  let body_owner f =
    match Generic_modules.member generics f.id with
    | None -> None
    | Some (group, application, _) ->
        Some (group, phys_equal application.source group.representative)
  in
  let body_module_context f =
    match body_owner f with
    | Some (group, _) -> context_for_group group
    | None -> Module_context.for_location module_contexts f.loc
  in
  let body_destination f =
    match body_owner f with
    | None -> (body_module_context f).destination
    | Some (group, _) -> Module_context.Worker group
  in
  let runtime_destinations =
    Module_context.Flat :: List.map generics ~f:(fun group -> Module_context.Worker group)
  in
  let with_body_names entries =
    entries
    @ List.filter_map funcs ~f:(fun f ->
        match body_owner f with
        | Some (_, true) ->
            Option.map
              (List.Assoc.find entries (proc_name f) ~equal:String.equal)
              ~f:(fun value -> (body_proc_name f, value))
        | Some (_, false) | None -> None)
  in
  let* procedure_signatures =
    all funcs ~f:(fun f ->
        let outputs = ghost_results f in
        let* () =
          match outputs with
          | (id, _) :: _ when is_pure f ->
              unsupported id.pid_loc "Ghost results of a pure function"
          | (id, _) :: _ when not f.manual ->
              unsupported id.pid_loc "Ghost results require a manual function proof"
          | _ -> Ok ()
        in
        let declared xs =
          all xs ~f:(fun (id, pty) ->
              let* t = Source.ocaml_type f.environment ~at:id.S.pid_loc pty in
              Ok (id.pid_str, t))
        in
        let* procedure_inputs = declared (ghost_params f) in
        let* procedure_outputs = declared outputs in
        Ok
          ( proc_name f,
            { procedure_inputs; procedure_outputs; procedure_result = f.body.exp_type } ))
  in
  let procedure_signatures = with_body_names procedure_signatures in
  let au_plan (au : Source.proof_au) =
    if Option.is_none au.au_application then asset_worker au.au_scope else None
  in
  let au_procedure au f =
    match au_plan au with Some _ -> body_proc_name f | None -> proc_name f
  in
  let au_application_view (au : Source.proof_au) =
    Option.bind au.au_application ~f:(fun (_, template) ->
        List.find scoped_proofs.applications ~f:(fun view ->
            match view.source.kind with
            | Atomic original ->
                Ident.same original.au_id template
                && Path.same au.au_path (Path.Pdot (view.path, au.au_name))
            | _ -> false))
  in
  let applied_atomic_operation (au : Source.proof_au) =
    let ( let* ) value f = Option.bind value ~f in
    let* identity, template = au.au_application in
    let* binding =
      List.find scoped_proofs.bindings ~f:(fun binding ->
          match binding.Proof_bindings.kind with
          | Atomic original -> Ident.same original.au_id template
          | _ -> false)
    in
    let* plan = Generic_proofs.owner generic_proofs (Some binding.entry.scope) in
    let* member =
      match binding.kind with
      | Atomic original -> Source.scoped_value_name plan.scope original.au_operation_path
      | _ -> None
    in
    let* application =
      List.find plan.group.applications ~f:(fun application ->
          Path.same application.source.identity identity)
    in
    let* id = List.Assoc.find application.source.members member ~equal:String.equal in
    List.find funcs ~f:(fun f -> Ident.same f.id id)
  in
  let* atomic_operations =
    all source.proof_aus ~f:(fun (au : Source.proof_au) ->
        let operation =
          match au_plan au with
          | None ->
              Option.first_some
                (List.find funcs ~f:(fun f ->
                     List.mem f.paths au.au_operation_path ~equal:Path.same))
                (applied_atomic_operation au)
          | Some plan ->
              Option.bind (Source.scoped_value_name plan.scope au.au_operation_path)
                ~f:(fun member ->
                  Option.bind
                    (List.Assoc.find plan.group.representative.members member
                       ~equal:String.equal) ~f:(fun id ->
                      List.find funcs ~f:(fun f -> Ident.same f.id id)))
        in
        match operation with
        | None ->
            error au.au_at "An AU facade must name a procedure in this implementation"
        | Some f when not (Option.exists f.contract ~f:(fun c -> c.atomic)) ->
            error au.au_at "An AU facade requires a logically atomic contract"
        | Some f -> Ok (au, f))
  in
  let token_types =
    List.map atomic_operations ~f:(fun (au, f) ->
        Datatypes.with_paths
          (Datatypes.atomic_token ~path:au.Source.au_token_path
             ~procedure:(au_procedure au f) ~at:au.au_at)
          au.au_token_paths)
  in
  let generic_models = Generic_proofs.model_types source inventory generic_proofs in
  let generic_model data =
    List.exists generic_proofs ~f:(fun plan ->
        List.exists (Generic_proofs.models source plan) ~f:(fun model ->
            Poly.equal model.Datatypes.at data.Datatypes.at))
  in
  let private_ra_type data =
    List.exists private_ra_types ~f:(fun (_, owned) ->
        Poly.equal data.Datatypes.at owned.Datatypes.at)
  in
  let data_types =
    List.filter types ~f:(fun data ->
        (not (generic_model data)) && not (private_ra_type data))
  in
  let resource_types =
    List.concat_map all_resource_views ~f:(fun r ->
        r.Source.resource_descriptor :: r.resource_aliases)
  in
  let* generic_runtime_types =
    all generic_proofs ~f:(fun plan ->
        let* layouts =
          Result_layouts.symbolic layouts plan.Generic_proofs.group
            ~owner:(String.split plan.group.name ~on:'.' @ [ "Layout" ])
        in
        Ok
          (List.filter_map (Generic_proofs.runtime_types plan) ~f:(fun declaration ->
               Option.map
                 (List.find layouts ~f:(fun descriptor ->
                      Option.exists descriptor.Datatypes.id ~f:(fun id ->
                          String.equal (Ident.name id) declaration.Typedtree.typ_name.txt)
                      && Poly.equal descriptor.at declaration.typ_loc))
                 ~f:(fun descriptor ->
                   {
                     descriptor with
                     id = Some declaration.typ_id;
                     paths = [];
                     library = None;
                   }))))
    |> Result.map ~f:List.concat
  in
  let types =
    generic_runtime_types
    @ List.map private_ra_types ~f:snd
    @ generic_models @ generic_proof_types @ types @ resource_types @ token_types
    @ source.logical_types
    @ match source.sequence with Pident id -> [ Datatypes.sequence id ] | _ -> []
  in
  (* Each data type's module, given the ones declared before it; a record type that is a
     reference has fields instead. *)
  let* modules =
    all
      (List.filter_mapi data_types ~f:(fun i (d : Datatypes.t) ->
           Option.some_if
             (Option.is_none d.heap && Option.is_none d.alias
             && not (Result_layouts.contains layouts d))
             (List.take data_types i, d)))
      ~f:(fun (before, d) ->
        let* member =
          Datatypes.member
            (generic_proof_types @ generic_models @ before @ resource_types @ token_types
           @ source.logical_types)
            d
        in
        Ok (d.Datatypes.module_name, member))
  in
  let proof_module path ~at =
    match
      List.find all_resources ~f:(fun resource -> Source.resource_has_path resource path)
    with
    | Some resource -> Ok resource
    | None -> error at "The proof module argument has no translated declaration"
  in
  let rec depends_on_definition seen resource =
    if Option.is_some resource.Source.resource_application then false
    else if List.mem seen resource.resource_id ~equal:Ident.same then false
    else if resource.resource_definition then true
    else
      let seen = resource.resource_id :: seen in
      let dependency path =
        List.exists source.proof_resources ~f:(fun argument ->
            (Path.same path argument.resource_path
            || Path.same path (Path.Pident argument.resource_id))
            && depends_on_definition seen argument)
      in
      Option.exists resource.resource_alias_of ~f:dependency
      || List.exists resource.resource_arguments ~f:(function
        | Source.Type_argument _ -> false
        | Module_argument path -> dependency path)
  in
  let deferred_resources =
    List.filter source.proof_resources ~f:(fun resource ->
        Option.is_none resource.Source.resource_application
        && Module_context.emits_owner module_contexts ~destination:Module_context.Flat
             resource.resource_scope
        && depends_on_definition [] resource)
  in
  let* native_resource_members =
    all
      (List.filter source.proof_resources ~f:(fun resource ->
           (not resource.Source.resource_abstract)
           && Option.is_none resource.resource_application))
      ~f:(fun resource ->
        let at = resource.Source.resource_at in
        let l = loc at in
        let* member =
          match (resource.resource_definition, resource.resource_alias_of) with
          | true, _ ->
              let* backend =
                match implementation resource with
                | Some backend -> Ok backend
                | None -> error at "Missing resource algebra implementation"
              in
              let interface =
                qualified_name ~loc:l (String.concat ~sep:"." resource.resource_functor)
              in
              Ok
                (R.Member.alias ~loc:l ~typ:interface ~sealed:true
                   (ident ~loc:l (Qualified_name.of_string resource.resource_backend).name)
                   (qualified_name ~loc:l backend))
          | false, Some path ->
              let* target = proof_module path ~at in
              Ok
                (R.Member.alias ~loc:l
                   (ident ~loc:l (Qualified_name.of_string resource.resource_backend).name)
                   (qualified_name ~loc:l target.resource_backend))
          | false, None ->
              let* arguments =
                all resource.resource_arguments ~f:(function
                  | Source.Type_argument typ -> Datatypes.typ types ~at typ
                  | Module_argument path ->
                      let* argument = proof_module path ~at in
                      Ok
                        (R.Type.named ~loc:l
                           (qualified_name ~loc:l argument.resource_backend)
                           []))
              in
              let library =
                qualified_name ~loc:l (String.concat ~sep:"." resource.resource_functor)
              in
              Ok
                (R.Member.instance ~loc:l ~def:(library, arguments)
                   (ident ~loc:l (Qualified_name.of_string resource.resource_backend).name)
                   library)
        in
        Ok (resource.resource_backend, member))
  in
  let imported_resource_members =
    List.filter_map source.proof_resources ~f:(fun resource ->
        if
          resource.Source.resource_abstract
          && Option.is_none resource.resource_scope
          && Option.is_none resource.resource_application
        then
          let l = loc resource.resource_at in
          Some
            (R.Member.free
               (R.Member.instance ~loc:l
                  (ident ~loc:l resource.resource_backend)
                  (qualified_name ~loc:l
                     (String.concat ~sep:"." resource.resource_functor))))
        else None)
  in
  let public_resource_members =
    List.filter_map
      (List.filter source.proof_resources ~f:(fun resource ->
           Option.is_none resource.Source.resource_application))
      ~f:(fun resource ->
        Option.map resource.Source.resource_public ~f:(fun public ->
            let l = loc public.resource_at in
            ( resource,
              R.Member.alias ~loc:l
                ~typ:
                  (qualified_name ~loc:l (String.concat ~sep:"." public.resource_functor))
                (ident ~loc:l (Qualified_name.of_string public.resource_backend).name)
                (qualified_name ~loc:l resource.resource_backend) )))
  in
  let proof_module_names =
    List.map source.proof_types ~f:(fun data -> data.Datatypes.module_name)
  in
  let runtime_modules =
    List.filter_map modules ~f:(fun (name, member) ->
        Option.some_if (not (List.mem proof_module_names name ~equal:String.equal)) member)
  in
  let proof_modules =
    List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
        match entry.Proof_scopes.declaration with
        | S.Proof_type _ ->
            Option.bind
              (List.find source.proof_types ~f:(fun data ->
                   Poly.equal data.Datatypes.at entry.name.pid_loc))
              ~f:(fun data ->
                List.Assoc.find modules data.module_name ~equal:String.equal)
        | Proof_resource _ ->
            Option.bind
              (List.find source.proof_resources ~f:(fun resource ->
                   Poly.equal resource.Source.resource_at entry.name.pid_loc
                   && Module_context.emits_owner module_contexts
                        ~destination:Module_context.Flat resource.resource_scope
                   && not (depends_on_definition [] resource)))
              ~f:(fun resource ->
                List.Assoc.find native_resource_members resource.resource_backend
                  ~equal:String.equal)
        | _ -> None)
  in
  let deferred_native_resource_members =
    List.filter_map deferred_resources ~f:(fun resource ->
        List.Assoc.find native_resource_members resource.resource_backend
          ~equal:String.equal)
  in
  let rec resource_dependencies seen resource =
    let application =
      List.find_map generics ~f:(fun group ->
          List.find_map group.Generic_modules.applications ~f:(fun application ->
              Option.some_if
                (List.is_prefix
                   (String.split resource.Source.resource_backend ~on:'.')
                   ~prefix:[ application.name ] ~equal:String.equal)
                application.name))
    in
    if Option.is_some application then Ok (Option.to_list application)
    else if List.mem seen resource.Source.resource_id ~equal:Ident.same then Ok []
    else
      let* aliases =
        match resource.resource_alias_of with
        | None -> Ok []
        | Some path ->
            let* target = proof_module path ~at:resource.resource_at in
            resource_dependencies (resource.resource_id :: seen) target
      in
      let* dependencies =
        all resource.resource_arguments ~f:(function
          | Source.Type_argument typ ->
              Ok
                (Result_layouts.type_dependencies
                   ~additional:(Generic_proofs.layout_dependencies generic_proofs)
                   layouts types typ)
          | Module_argument path ->
              let* argument = proof_module path ~at:resource.resource_at in
              resource_dependencies (resource.resource_id :: seen) argument)
      in
      Ok (aliases @ List.concat dependencies)
  in
  let* module_declarations =
    all (runtime_modules @ proof_modules) ~f:(fun member ->
        let* dependencies =
          match
            List.find modules ~f:(fun (_, candidate) -> phys_equal member candidate)
          with
          | Some (source_name, _) ->
              let data =
                List.find_exn data_types ~f:(fun d ->
                    String.equal d.Datatypes.module_name source_name)
              in
              Ok
                (Result_layouts.dependencies
                   ~additional:(Generic_proofs.layout_dependencies generic_proofs)
                   layouts types data)
          | None ->
              let resource_name =
                fst
                  (List.find_exn native_resource_members ~f:(fun (_, candidate) ->
                       phys_equal member candidate))
              in
              let resource =
                List.find_exn source.proof_resources ~f:(fun r ->
                    String.equal r.Source.resource_backend resource_name)
              in
              resource_dependencies [] resource
        in
        Ok (dependencies, [ member ]))
  in
  let* field_declarations =
    all
      (List.filter types ~f:(fun d ->
           (not (Result_layouts.contains layouts d))
           && not (List.mem generic_runtime_types d ~equal:phys_equal)))
      ~f:(fun d ->
        let* fields = Datatypes.fields ~declarations:[ d ] types in
        Ok
          ( Result_layouts.dependencies
              ~additional:(Generic_proofs.layout_dependencies generic_proofs)
              layouts types d,
            fields ))
  in
  let pending_declarations = ref (module_declarations @ field_declarations) in
  let available_layouts = ref [] in
  let take_declarations () =
    let ready, pending =
      List.partition_tf !pending_declarations ~f:(fun (dependencies, _) ->
          List.for_all dependencies ~f:(fun name ->
              List.mem !available_layouts name ~equal:String.equal))
    in
    pending_declarations := pending;
    List.concat_map ready ~f:snd
  in
  let modules = take_declarations () in
  let refs = ref [] in
  let primitives = ref [] in
  let functions =
    Path_bindings.of_list
      (List.concat_map funcs ~f:(fun f ->
           List.map f.paths ~f:(fun path -> (path, proc_name f)))
      @ List.concat_map checked_operations ~f:(fun operation ->
          List.map operation.operation_paths ~f:(fun path ->
              (path, operation.operation_name))))
  in
  let lifted =
    List.filter_map funcs ~f:(fun f ->
        Option.some_if
          ((not (List.is_empty f.prefix))
          || (not (List.is_empty f.captured))
          || Option.is_some f.role)
          (proc_name f, (f.prefix_count, f.captured, f.role)))
  in
  let origins = ref [] in
  let ocaml_env = source.env in
  (* The predicates' signatures first, for their bodies and the contracts to use. *)
  let* predicates = predicates ~data:types source in
  let* () = check_scoped_resources ~types source inventory scoped_proofs in
  let* applications =
    all scoped_proofs.applications ~f:(fun view ->
        let formal =
          List.find_map (List.rev view.constraints) ~f:(fun constraint_ ->
              List.Assoc.find constraint_.Module_inventory.signature.signature_resources
                view.source.entry.name.pid_str ~equal:String.equal
              |> Option.map ~f:(fun formal -> (constraint_, formal)))
        in
        match (formal, view.source.kind) with
        | Some (constraint_, formal), Predicate _ ->
            let environment =
              Source.annotation_env source formal.Module_inventory.site.environment
            in
            let* raw =
              Proof_bindings.parameter_types environment formal.declaration.pred_params
            in
            let projection =
              Proof_bindings.signature_type_projection Subst.identity view.path
                constraint_.signature
            in
            Ok { view with types = List.map raw ~f:(Subst.type_expr projection) }
        | _ -> Ok view)
  in
  let scoped_proofs = Proof_bindings.with_applications scoped_proofs applications in
  let* scoped_predicates =
    all (List.filter_map scoped_proofs.bindings ~f:scoped_predicate)
      ~f:(fun ((_, p, _, ts) as declaration) ->
        let* _ = predicate_output_count types p ts in
        Ok declaration)
  in
  let* scoped_inputs =
    all scoped_predicates ~f:(fun (_, p, _, ts) ->
        let* outputs = predicate_output_count types p ts in
        Ok (p.pred_name.pid_str, List.length ts - outputs))
  in
  let predicates = predicates @ scoped_predicates in
  (* The abstract predicates of the libraries, by their qualified names, as [Cell.holds],
     whose parameters' types are the library's own where it declares them. *)
  let* library_preds =
    all libraries ~f:(fun (lib : Library_modules.t) ->
        let* environment = Library_modules.environment source lib in
        all
          (List.filter
             (Annotation.of_comments lib.library.interface_comments)
             ~f:(Annotation.predicate_declaration ~interface:true))
          ~f:(fun a ->
            let* p = Annotation.predicate a in
            let* () =
              match p.pred_body with
              | Some _ -> unsupported a.loc "A predicate of a library with a definition"
              | None -> Ok ()
            in
            let* types =
              all p.pred_params ~f:(fun (_, t) ->
                  Source.ocaml_type environment ~at:a.loc t)
            in
            Ok (lib, p, types)))
  in
  let library_preds = List.concat library_preds in
  let resource_signatures =
    List.map library_preds ~f:(fun (lib, p, ts) ->
        {
          resource_paths =
            [ Path.Pdot (lib.Library_modules.library_path, p.S.pred_name.pid_str) ];
          resource_declaration = p;
          resource_backend = lib.library_name ^ "." ^ p.pred_name.pid_str;
          resource_types = ts;
          resource_raw_types = ts;
        })
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        match (binding.Proof_bindings.kind, binding.entry.scope.owner) with
        | Predicate (p, _), Some owner when binding.exported ->
            let declaration =
              Proof_bindings.constraints_for scoped_proofs binding
              |> List.filter ~f:(fun constraint_ ->
                  constraint_.Module_inventory.restricts_visibility)
              |> List.rev
              |> List.find_map ~f:(fun constraint_ ->
                  List.Assoc.find
                    constraint_.Module_inventory.signature.signature_resources
                    binding.entry.name.pid_str ~equal:String.equal)
              |> Option.value_map ~default:p ~f:(fun formal ->
                  formal.Module_inventory.declaration)
            in
            let original = Path.Pdot (owner, binding.entry.name.pid_str) in
            let paths =
              List.fold inventory.aliases ~init:[ original ]
                ~f:(fun paths (alias, target) ->
                  paths @ List.filter_map paths ~f:(alias_path ~alias ~target))
            in
            Some
              {
                resource_paths = paths;
                resource_declaration = declaration;
                resource_backend = binding.backend;
                resource_types = binding.public_types;
                resource_raw_types = binding.public_types;
              }
        | _ -> None)
  in
  let resource_signatures =
    resource_signatures
    @ List.filter_map scoped_proofs.applications ~f:(fun view ->
        match view.Proof_bindings.source.kind with
        | Predicate (p, _)
          when Proof_bindings.application_visible scoped_proofs ~scope:None view ->
            Some
              {
                resource_paths = [ Path.Pdot (view.path, view.source.entry.name.pid_str) ];
                resource_declaration = p;
                resource_backend = view.backend;
                resource_types = view.types;
                resource_raw_types = view.types;
              }
        | _ -> None)
  in
  let* checked_views, _ =
    List.fold_result inventory.bindings ~init:([], resource_signatures)
      ~f:(fun (views, resources) binding ->
        let source_path = List.hd_exn binding.Module_inventory.paths in
        let source_substitution = checked_type_substitution binding source_path in
        let actual_substitution =
          checked_type_substitution ~substitution:binding.parameter_substitution binding
            binding.actual_path
        in
        let view_types = checked_raw_types types binding in
        let* view_resources =
          all binding.expected.signature_resources ~f:(fun (member, formal) ->
              let wanted = Path.Pdot (binding.actual_path, member) in
              match
                List.find resources ~f:(fun resource ->
                    List.mem resource.resource_paths wanted ~equal:Path.same)
              with
              | None ->
                  error binding.site.item_loc
                    ("The actual module does not declare resource " ^ member)
              | Some actual ->
                  let declaration = formal.Module_inventory.declaration in
                  let* () =
                    if Option.is_none declaration.pred_body then Ok ()
                    else
                      unsupported formal.site.item_loc
                        "A resource definition in a checked module signature"
                  in
                  let* () =
                    if
                      Bool.equal declaration.pred_persistent
                        actual.resource_declaration.pred_persistent
                      && List.length declaration.pred_params
                         = List.length actual.resource_types
                    then Ok ()
                    else
                      error binding.site.item_loc
                        ("The resource declaration " ^ member
                       ^ " has a different kind or arity")
                  in
                  let environment =
                    Source.annotation_env source formal.site.environment
                  in
                  let* raw =
                    all declaration.pred_params ~f:(fun (id, pty) ->
                        Source.ocaml_type environment ~at:id.S.pid_loc pty)
                  in
                  let projected = List.map raw ~f:(Subst.type_expr actual_substitution) in
                  let* () =
                    if
                      List.for_all2_exn projected actual.resource_types
                        ~f:(fun expected actual ->
                          Ctype.is_equal binding.site.environment false [ expected ]
                            [ Subst.type_expr binding.parameter_substitution actual ])
                    then Ok ()
                    else
                      error binding.site.item_loc
                        ("The resource declaration " ^ member
                       ^ " has different parameter types")
                  in
                  let* expected_modes =
                    implicit_parameter_count ~kind:"predicate" declaration.pred_params
                  in
                  let* actual_modes =
                    implicit_parameter_count ~kind:"predicate"
                      actual.resource_declaration.pred_params
                  in
                  let* expected_outputs =
                    predicate_output_count view_types declaration raw
                  in
                  let* actual_outputs =
                    predicate_output_count types actual.resource_declaration
                      actual.resource_types
                  in
                  let* () =
                    if
                      Poly.equal expected_modes actual_modes
                      && expected_outputs = actual_outputs
                    then Ok ()
                    else
                      error binding.site.item_loc
                        ("The resource declaration " ^ member
                       ^ " has different implicit parameter modes")
                  in
                  Ok
                    ( formal,
                      {
                        resource_paths =
                          List.map binding.paths ~f:(fun path -> Path.Pdot (path, member));
                        resource_declaration = declaration;
                        resource_backend = actual.resource_backend;
                        resource_types =
                          List.map raw ~f:(Subst.type_expr source_substitution);
                        resource_raw_types = raw;
                      } ))
        in
        let view =
          {
            view_binding = binding;
            view_key =
              fresh
                ("view$" ^ String.uncapitalize (String.concat ~sep:"_" binding.namespace));
            view_resources;
            view_source_substitution = source_substitution;
            view_actual_substitution = actual_substitution;
            view_types;
          }
        in
        let aliases =
          List.concat_map view_resources ~f:(fun (_, resource) ->
              List.map resource.resource_paths ~f:(fun path ->
                  match path with
                  | Path.Pdot (parent, _) ->
                      {
                        resource with
                        resource_paths = [ path ];
                        resource_types =
                          List.map resource.resource_raw_types
                            ~f:
                              (Subst.type_expr (checked_type_substitution binding parent));
                      }
                  | _ -> resource))
        in
        Ok (views @ [ view ], resources @ aliases))
  in
  let checked_resource_entries =
    List.concat_map checked_views ~f:(fun view ->
        List.concat_map view.view_resources ~f:(fun (_, resource) ->
            List.mapi resource.resource_paths ~f:(fun index path ->
                let ts =
                  match path with
                  | Path.Pdot (parent, _) ->
                      List.map resource.resource_raw_types
                        ~f:
                          (Subst.type_expr
                             (checked_type_substitution view.view_binding parent))
                  | _ -> resource.resource_types
                in
                let key =
                  view.view_key ^ "_" ^ Int.to_string index ^ "."
                  ^ resource.resource_declaration.pred_name.pid_str
                in
                (path, key, resource, ts))))
  in
  let checked_preds =
    List.map checked_resource_entries ~f:(fun (_, key, resource, ts) ->
        (key, (resource.resource_backend, ts)))
  in
  let* predicate_inputs =
    all
      (List.map predicates ~f:(fun (_, p, _, ts) -> (p.S.pred_name.pid_str, p, ts))
      @ List.map library_preds ~f:(fun ((lib : Library_modules.t), p, ts) ->
          (lib.source_name ^ "." ^ p.S.pred_name.pid_str, p, ts)))
      ~f:(fun (key, p, ts) ->
        let* count = implicit_parameter_count ~kind:"predicate" p.pred_params in
        Ok (Option.map count ~f:(fun count -> (key, List.length ts - count))))
  in
  let predicate_inputs = List.filter_opt predicate_inputs in
  let predicate_inputs =
    predicate_inputs
    @ List.filter_map library_preds ~f:(fun (lib, p, _) ->
        Option.map
          (List.Assoc.find predicate_inputs
             (lib.Library_modules.source_name ^ "." ^ p.S.pred_name.pid_str)
             ~equal:String.equal)
          ~f:(fun count -> (lib.library_name ^ "." ^ p.pred_name.pid_str, count)))
  in
  let* checked_inputs =
    all checked_resource_entries ~f:(fun (_, key, resource, ts) ->
        let* count =
          implicit_parameter_count ~kind:"predicate"
            resource.resource_declaration.pred_params
        in
        Ok
          (Option.map
             (Option.first_some
                (Option.map count ~f:(fun count -> List.length ts - count))
                (List.Assoc.find scoped_inputs resource.resource_backend
                   ~equal:String.equal))
             ~f:(fun count -> (key, count))))
  in
  let predicate_inputs = List.filter_opt checked_inputs @ predicate_inputs in
  let preds =
    List.map predicates ~f:(fun (_, p, _, types) ->
        (p.pred_name.pid_str, (p.pred_name.pid_str, types)))
    @ List.map library_preds ~f:(fun ((lib : Library_modules.t), p, types) ->
        let key = lib.source_name ^ "." ^ p.pred_name.pid_str in
        (key, (lib.library_name ^ "." ^ p.pred_name.pid_str, types)))
  in
  let preds =
    preds
    @ List.filter_map preds ~f:(fun (_, (target, types)) ->
        if List.Assoc.mem preds target ~equal:String.equal then None
        else Some (target, (target, types)))
  in
  let preds = checked_preds @ preds in
  let scoped_keys = List.map scoped_proofs.bindings ~f:(fun binding -> binding.backend) in
  let private_scoped_inputs = scoped_inputs in
  let predicate_inputs =
    List.filter predicate_inputs ~f:(fun (key, _) ->
        not (List.mem scoped_keys key ~equal:String.equal))
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        if binding.exported then
          Option.map
            (List.Assoc.find private_scoped_inputs binding.backend ~equal:String.equal)
            ~f:(fun count -> (binding.public_key, count))
        else None)
  in
  let preds =
    List.filter preds ~f:(fun (key, _) ->
        not (List.mem scoped_keys key ~equal:String.equal))
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        match binding.kind with
        | Predicate _ when binding.exported ->
            Some (binding.public_key, (binding.backend, binding.public_types))
        | _ -> None)
  in
  let logical_declarations =
    List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
        match entry.Proof_scopes.declaration with
        | S.Proof_function _ as declaration ->
            if Option.is_none entry.scope.owner then Some declaration
            else
              Option.bind
                (List.find scoped_proofs.bindings ~f:(fun binding ->
                     Ident.same binding.entry.id entry.id))
                ~f:scoped_function
        | _ -> None)
  in
  let* all_logical_functions =
    all logical_declarations ~f:(function
      | S.Proof_function { function_name; function_params; function_result; _ } ->
          let ocaml_env = declaration_environment function_name.pid_str in
          let* lemma_inputs =
            all function_params ~f:(fun (id, ty) ->
                Source.ocaml_type ocaml_env ~at:id.S.pid_loc ty)
          in
          let* output =
            Source.ocaml_type ocaml_env ~at:function_name.pid_loc function_result
          in
          Ok
            ( function_name.pid_str,
              {
                lemma_raven = function_name.pid_str;
                lemma_constant = List.is_empty function_params;
                lemma_inputs;
                lemma_implicit_count = 0;
                lemma_outputs = [ output ];
              } )
      | _ -> error Location.none "Expected a logical function declaration")
  in
  let logical_functions =
    List.filter all_logical_functions ~f:(fun (key, _) ->
        Option.is_none (scoped_binding key))
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        match binding.kind with
        | Function (S.Proof_function declaration) when binding.exported ->
            let inputs, outputs =
              List.split_n binding.public_types (List.length declaration.function_params)
            in
            let signature =
              List.Assoc.find_exn all_logical_functions binding.backend
                ~equal:String.equal
            in
            Some
              ( binding.public_key,
                { signature with lemma_inputs = inputs; lemma_outputs = outputs } )
        | _ -> None)
  in
  let resources, ghost_fields = proof_assets None in
  let proof_support =
    {
      runtime_functions =
        Path_bindings.of_list
          (List.concat_map pure ~f:(fun f ->
               List.filter_map f.paths ~f:(fun path ->
                   match path with
                   | Path.Pdot _ when not (List.is_empty f.signature_sites) -> None
                   | _ -> Some (path, pure_reference f))));
      predicate_views =
        Path_bindings.of_list
          (List.map checked_resource_entries ~f:(fun (path, key, _, _) -> (path, key)));
      public_types;
      strict_source_types = false;
      library_paths = library_paths libraries;
      atomic_updates = [];
      resources;
      ghost_fields;
      canonical_path = Proof_bindings.canonical_owner scoped_proofs;
      logical_functions;
      mathematical_types =
        generic_models @ source.proof_types @ source.logical_types @ resource_types
        @ token_types;
      predicate_inputs;
      proof_key =
        (fun environment q ->
          Proof_bindings.resolve scoped_proofs ~scope:None ~environment q);
      action_key =
        (fun id ->
          Proof_bindings.action_key scoped_proofs
            ~scope:(Proof_bindings.scope_for_location scoped_proofs id.S.pid_loc)
            id);
      opaque_predicates =
        Proof_bindings.opaque_keys scoped_proofs
        @ List.map checked_resource_entries ~f:(fun (_, key, _, _) -> key)
        @ List.concat_map library_preds ~f:(fun (library, p, _) ->
            [
              library.Library_modules.source_name ^ "." ^ p.pred_name.pid_str;
              library.library_name ^ "." ^ p.pred_name.pid_str;
            ]);
    }
  in
  let spec_funcs =
    List.map pure ~f:(fun f ->
        (String.concat ~sep:"." (f.namespace @ [ Ident.name f.id ]), pure_name f))
    @ List.map preds ~f:(fun (p, (raven, _)) -> (p, raven))
    @ List.map logical_functions ~f:(fun (n, s) -> (n, s.lemma_raven))
  in
  let atomic_predicates signatures =
    List.concat_map signatures ~f:(fun signature ->
        List.map [ "pending"; "committed" ] ~f:(fun method_ ->
            let inputs, _ = Option.value_exn (atomic_inputs signature method_) in
            let key = signature.au_key ^ "." ^ method_ in
            (key, (key, inputs))))
  in
  let context_atomic ?current_procedure scope signatures =
    let environment =
      Option.value_map scope ~default:source.env ~f:(fun scope ->
          Source.annotation_env source scope.Proof_scopes.environment)
    in
    let public = Proof_bindings.public_type scoped_proofs in
    let rebase = Proof_bindings.context_type scoped_proofs ~environment in
    let inside owner =
      match (owner, scope) with
      | None, _ -> true
      | Some owner, Some caller ->
          Option.exists (Proof_scopes.find_owner source.proof_scopes (Some owner))
            ~f:(fun parent ->
              Option.is_some
                (Proof_bindings.drop_prefix parent.namespace caller.Proof_scopes.namespace))
      | Some _, None -> false
    in
    List.filter_map signatures ~f:(fun signature ->
        let au = signature.au_source in
        let binding =
          List.find scoped_proofs.bindings ~f:(fun binding ->
              match binding.kind with
              | Atomic actual -> Ident.same actual.au_id au.au_id
              | _ -> false)
        in
        if
          match au.au_application with
          | None ->
              Option.exists binding ~f:(fun binding ->
                  not (Proof_bindings.visible scoped_proofs ~scope binding))
          | Some _ ->
              not
                (Option.exists (au_application_view au)
                   ~f:(Proof_bindings.application_visible scoped_proofs ~scope))
        then None
        else
          let private_operation =
            Option.equal String.equal current_procedure (Some signature.au_procedure)
            || inside signature.au_owner
          in
          let project =
            if private_operation then Fn.id else fun ty -> rebase (public ty)
          in
          let token =
            if inside au.au_scope then au.au_token else rebase (public au.au_token)
          in
          Some
            {
              signature with
              au_token = token;
              au_inputs = List.map signature.au_private.inputs ~f:project;
              au_result = project signature.au_private.result;
              au_ghost_outputs = List.map signature.au_private.ghost_outputs ~f:project;
              au_implicit = List.map signature.au_private.implicit ~f:project;
            })
  in
  let context_owners at =
    Option.value_map at ~default:[] ~f:(Proof_scopes.owners_at source.proof_scopes)
  in
  let proof_context ?current_procedure ?at scope preds spec_funcs proof_support =
    let owners = context_owners at in
    let atomic_updates =
      context_atomic ?current_procedure scope proof_support.atomic_updates
    in
    let atomic_keys = List.map (atomic_predicates proof_support.atomic_updates) ~f:fst in
    let atomic_preds = atomic_predicates atomic_updates in
    let preds =
      List.filter preds ~f:(fun (key, _) ->
          not (List.mem atomic_keys key ~equal:String.equal))
      @ atomic_preds
    in
    let spec_funcs =
      List.filter spec_funcs ~f:(fun (key, _) ->
          not (List.mem atomic_keys key ~equal:String.equal))
      @ List.map atomic_preds ~f:(fun (key, _) -> (key, key))
    in
    let proof_support = { proof_support with atomic_updates } in
    let resources, ghost_fields = proof_assets scope in
    let proof_support = { proof_support with resources; ghost_fields } in
    let environment =
      Option.value_map scope ~default:source.env ~f:(fun scope ->
          Source.annotation_env source scope.Proof_scopes.environment)
    in
    let project = Proof_bindings.context_type scoped_proofs ~environment in
    let local_exports = Proof_bindings.local_exports scoped_proofs ~scope in
    let preds =
      List.filter_map local_exports ~f:(fun binding ->
          match binding.kind with
          | Predicate _ ->
              Some (binding.public_key, (binding.backend, binding.public_types))
          | Lemma _ | Function _ | Resource _ | Field _ | Atomic _ | State _ | Action _ ->
              None)
      @ preds
    in
    let predicate_inputs =
      List.filter_map local_exports ~f:(fun binding ->
          Option.map (List.Assoc.find scoped_inputs binding.backend ~equal:String.equal)
            ~f:(fun count -> (binding.public_key, count)))
      @ proof_support.predicate_inputs
    in
    let logical_functions =
      List.filter_map local_exports ~f:(fun binding ->
          match binding.kind with
          | Function (S.Proof_function declaration) ->
              let inputs, outputs =
                List.split_n binding.public_types
                  (List.length declaration.function_params)
              in
              let signature =
                List.Assoc.find_exn all_logical_functions binding.backend
                  ~equal:String.equal
              in
              Some
                ( binding.public_key,
                  { signature with lemma_inputs = inputs; lemma_outputs = outputs } )
          | _ -> None)
      @ proof_support.logical_functions
    in
    let opaque_predicates =
      List.filter proof_support.opaque_predicates ~f:(fun key ->
          not
            (List.exists scoped_proofs.bindings ~f:(fun binding ->
                 String.equal binding.public_key key
                 && not (Proof_bindings.opaque_at scoped_proofs ~scope binding))))
      @ List.filter_map local_exports ~f:(fun binding ->
          Option.some_if
            (Proof_bindings.opaque_at scoped_proofs ~scope binding)
            binding.public_key)
    in
    let proof_support =
      { proof_support with predicate_inputs; logical_functions; opaque_predicates }
    in
    let spec_funcs =
      List.map logical_functions ~f:(fun (key, signature) -> (key, signature.lemma_raven))
      @ List.map preds ~f:(fun (key, (backend, _)) -> (key, backend))
      @ spec_funcs
    in
    let preds =
      List.map preds ~f:(fun (key, (backend, types)) ->
          (key, (backend, List.map types ~f:project)))
    in
    let logical_functions =
      List.map proof_support.logical_functions ~f:(fun (key, signature) ->
          ( key,
            {
              signature with
              lemma_inputs = List.map signature.lemma_inputs ~f:project;
              lemma_outputs = List.map signature.lemma_outputs ~f:project;
            } ))
    in
    let proof_support = { proof_support with logical_functions } in
    let application_views =
      List.filter scoped_proofs.applications
        ~f:(Proof_bindings.application_visible ~owners scoped_proofs ~scope)
    in
    let application_preds =
      List.filter_map application_views ~f:(fun view ->
          match view.source.kind with
          | Predicate _ -> Some (view.key, (view.backend, List.map view.types ~f:project))
          | _ -> None)
    in
    let application_inputs =
      List.filter_map application_views ~f:(fun view ->
          Option.map
            (List.Assoc.find scoped_inputs view.source.backend ~equal:String.equal)
            ~f:(fun count -> (view.key, count)))
    in
    let application_functions =
      List.filter_map application_views ~f:(fun view ->
          match view.source.kind with
          | Function _ ->
              Option.map
                (List.Assoc.find all_logical_functions view.source.backend
                   ~equal:String.equal) ~f:(fun signature ->
                  let inputs, outputs =
                    List.split_n view.types (List.length signature.lemma_inputs)
                  in
                  ( view.key,
                    {
                      signature with
                      lemma_raven = view.backend;
                      lemma_inputs = List.map inputs ~f:project;
                      lemma_outputs = List.map outputs ~f:project;
                    } ))
          | _ -> None)
    in
    let proof_support =
      {
        proof_support with
        logical_functions = application_functions @ proof_support.logical_functions;
      }
    in
    let spec_funcs =
      List.map application_functions ~f:(fun (key, signature) ->
          (key, signature.lemma_raven))
      @ spec_funcs
    in
    let preds = application_preds @ preds in
    let spec_funcs =
      List.map application_preds ~f:(fun (key, (backend, _)) -> (key, backend))
      @ spec_funcs
    in
    let proof_support =
      {
        proof_support with
        predicate_inputs = application_inputs @ proof_support.predicate_inputs;
        opaque_predicates =
          List.filter_map application_views ~f:(fun view ->
              Option.some_if
                (Proof_bindings.application_opaque ~owners scoped_proofs ~scope view)
                view.key)
          @ proof_support.opaque_predicates;
      }
    in
    let bindings = Proof_bindings.private_bindings scoped_proofs ~scope in
    let private_preds =
      List.filter_map bindings ~f:(fun binding ->
          match binding.kind with
          | Predicate _ ->
              Some
                ( binding.backend,
                  ( Option.value (definition_target binding) ~default:binding.backend,
                    binding.private_types ) )
          | Lemma _ | Function _ | Resource _ | Field _ | Atomic _ | State _ | Action _ ->
              None)
    in
    let inputs =
      List.filter_map bindings ~f:(fun binding ->
          Option.map
            (List.Assoc.find private_scoped_inputs binding.backend ~equal:String.equal)
            ~f:(fun count -> (binding.backend, count)))
    in
    let private_functions =
      List.filter_map bindings ~f:(fun binding ->
          Option.map
            (List.Assoc.find all_logical_functions binding.backend ~equal:String.equal)
            ~f:(fun signature ->
              ( binding.backend,
                {
                  signature with
                  lemma_raven =
                    Option.value (definition_target binding)
                      ~default:signature.lemma_raven;
                } )))
    in
    ( private_preds @ preds,
      List.filter_map bindings ~f:(fun binding ->
          match binding.kind with
          | Function _ ->
              Some
                ( binding.entry.name.pid_str,
                  Option.value (definition_target binding) ~default:binding.backend )
          | Predicate _ | Lemma _ | Resource _ | Field _ | Atomic _ | State _ | Action _
            ->
              None)
      @ List.map private_functions ~f:(fun (key, signature) ->
          (key, signature.lemma_raven))
      @ List.map private_preds ~f:(fun (key, (backend, _)) -> (key, backend))
      @ spec_funcs,
      {
        proof_support with
        proof_key =
          (fun environment q ->
            Proof_bindings.resolve ~owners scoped_proofs ~scope ~environment q);
        predicate_inputs = inputs @ proof_support.predicate_inputs;
        logical_functions = private_functions @ proof_support.logical_functions;
      } )
  in
  let* module_parameters =
    all module_contexts.contexts ~f:(fun context ->
        let* resources =
          all context.Module_context.parameters ~f:(fun parameter ->
              let generic = parameter.Generic_proofs.generic in
              let signature = parameter.instance.argument.expected in
              let original =
                Option.value parameter.original ~default:parameter.instance.parameter
              in
              let substitution =
                List.fold signature.signature_types ~init:Subst.identity
                  ~f:(fun substitution (name, declaration) ->
                    Subst.add_type declaration.Typedtree.typ_id
                      (Path.Pdot (Path.Pident original, name))
                      substitution)
              in
              let substitution =
                List.fold signature.signature_ghost_modules ~init:substitution
                  ~f:(fun substitution (name, formal) ->
                    let resource = formal.Module_inventory.ghost_resource in
                    let owner = Path.Pdot (Path.Pident original, name) in
                    let substitution =
                      Subst.add_module resource.resource_id owner substitution
                    in
                    List.fold resource.resource_type_members ~init:substitution
                      ~f:(fun substitution (member, id, _) ->
                        Subst.add_type id
                          (Path.Pdot (owner, String.uncapitalize member))
                          substitution))
              in
              let* resources =
                all signature.signature_resources ~f:(fun (name, formal) ->
                    let environment =
                      Source.annotation_env source
                        formal.Module_inventory.site.environment
                    in
                    let* ts =
                      all formal.declaration.pred_params ~f:(fun (id, ty) ->
                          Source.ocaml_type environment ~at:id.S.pid_loc ty)
                    in
                    let ts = List.map ts ~f:(Subst.type_expr substitution) in
                    let* outputs = predicate_output_count types formal.declaration ts in
                    let stem =
                      List.Assoc.find_exn generic.resources name ~equal:String.equal
                    in
                    let key =
                      Module_context.member context (generic.parameter ^ "." ^ stem)
                    in
                    Ok
                      ( (name, [ original; parameter.instance.parameter ]),
                        key,
                        ts,
                        List.length ts - outputs ))
              in
              Ok resources)
        in
        Ok (context, List.concat resources))
  in
  let module_context context ~projection (preds, spec_funcs, support) =
    let project =
      if List.is_empty context.Module_context.parameters then Fn.id
      else Subst.type_expr projection
    in
    let target backend =
      match scoped_binding backend with
      | Some binding when Module_context.contains context binding ->
          Module_context.member context backend
      | _ -> backend
    in
    let parameters = List.Assoc.find_exn module_parameters context ~equal:phys_equal in
    let preds =
      List.map preds ~f:(fun (key, (backend, ts)) ->
          (key, (target backend, List.map ts ~f:project)))
    in
    let preds =
      List.map parameters ~f:(fun (_, key, ts, _) -> (key, (key, List.map ts ~f:project)))
      @ preds
    in
    let spec_funcs =
      List.map parameters ~f:(fun (_, key, _, _) -> (key, key))
      @ List.map spec_funcs ~f:(fun (key, backend) -> (key, target backend))
    in
    let predicate_views =
      List.fold parameters ~init:support.predicate_views
        ~f:(fun views ((name, parameters), key, _, _) ->
          List.fold parameters ~init:views ~f:(fun views parameter ->
              Path_bindings.add views (Path.Pdot (Path.Pident parameter, name)) key))
    in
    ( preds,
      spec_funcs,
      {
        support with
        predicate_views;
        resources =
          List.map support.resources ~f:(fun resource ->
              {
                resource with
                resource_type = project resource.Source.resource_type;
                resource_path = Subst.module_path projection resource.resource_path;
                resource_operations =
                  List.map resource.resource_operations ~f:(fun (name, inputs, output) ->
                      (name, List.map inputs ~f:project, project output));
              });
        ghost_fields =
          List.map support.ghost_fields ~f:(fun field ->
              {
                field with
                field_owner = project field.Source.field_owner;
                field_value = project field.field_value;
                field_resource =
                  Option.map field.field_resource ~f:(Subst.module_path projection);
              });
        atomic_updates =
          List.map support.atomic_updates ~f:(fun signature ->
              {
                signature with
                au_token = project signature.au_token;
                au_inputs = List.map signature.au_inputs ~f:project;
                au_result = project signature.au_result;
                au_ghost_outputs = List.map signature.au_ghost_outputs ~f:project;
                au_implicit = List.map signature.au_implicit ~f:project;
              });
        logical_functions =
          List.map support.logical_functions ~f:(fun (key, signature) ->
              ( key,
                {
                  signature with
                  lemma_raven = target signature.lemma_raven;
                  lemma_inputs = List.map signature.lemma_inputs ~f:project;
                  lemma_outputs = List.map signature.lemma_outputs ~f:project;
                } ));
        predicate_inputs =
          List.map parameters ~f:(fun (_, key, _, inputs) -> (key, inputs))
          @ support.predicate_inputs;
        opaque_predicates =
          List.map parameters ~f:(fun (_, key, _, _) -> key) @ support.opaque_predicates;
      } )
  in
  let proof_context_for ~preds ~spec_funcs ~proof_support name =
    let context = declaration_context name in
    module_context context ~projection:Subst.identity
      (proof_context (declaration_scope name) preds spec_funcs proof_support)
  in
  let* atomic_updates =
    all atomic_operations ~f:(fun (au_source, f) ->
        let preds, spec_funcs, proof_support =
          proof_context ~current_procedure:(proc_name f) ~at:f.loc
            (Proof_bindings.scope_for_location scoped_proofs f.loc)
            preds spec_funcs proof_support
        in
        let preds, spec_funcs, proof_support =
          let context = asset_context au_source.Source.au_scope in
          module_context context ~projection:context.projection
            (preds, spec_funcs, proof_support)
        in
        let ctx =
          spec_context types ~refs ~primitives ~shared:no_shared ~ocaml_env:f.environment
            ~preds ~spec_funcs ~proof_support origins
        in
        let* formals = formals ctx f in
        let* _, _, implicit, _ =
          contract_env ctx ~spec_funcs f formals ~result:"result"
        in
        let signature =
          List.Assoc.find_exn procedure_signatures (proc_name f) ~equal:String.equal
        in
        let au_inputs =
          List.filter_map f.params ~f:(fun p ->
              match p.fp_kind with Tparam_pat pat -> Some pat.pat_type | _ -> None)
          @ List.map signature.procedure_inputs ~f:snd
        in
        let project =
          match au_plan au_source with
          | Some plan -> Subst.type_expr (Generic_proofs.source_projection plan)
          | None ->
              begin match Generic_modules.member generics f.id with
              | Some (_, application, _) ->
                  let path =
                    match au_source.au_operation_path with
                    | Path.Pdot (owner, _) -> owner
                    | _ -> application.source.identity
                  in
                  Subst.type_expr
                    (Generic_proofs.implementation_projection application.source path)
              | None -> Fn.id
              end
        in
        let shape =
          {
            inputs = List.map au_inputs ~f:project;
            result = project f.body.exp_type;
            ghost_outputs =
              List.map signature.procedure_outputs ~f:(fun (_, ty) -> project ty);
            implicit = List.map implicit ~f:(fun (_, _, ty, _) -> project ty);
          }
        in
        let key =
          Option.first_some
            (Option.map (au_application_view au_source) ~f:(fun view -> view.key))
            (List.find_map scoped_proofs.bindings ~f:(fun binding ->
                 match binding.kind with
                 | Atomic actual when Ident.same actual.au_id au_source.au_id ->
                     Some binding.backend
                 | _ -> None))
          |> Option.value ~default:au_source.au_name
        in
        let owner =
          match au_plan au_source with
          | Some plan -> plan.scope.owner
          | None ->
              begin match Proof_bindings.scope_for_location scoped_proofs f.loc with
              | Some scope when List.equal String.equal scope.namespace f.namespace ->
                  scope.owner
              | _ ->
                  List.find_map f.paths ~f:(function
                    | Path.Pdot (owner, _) ->
                        Some (Proof_bindings.canonical_owner scoped_proofs owner)
                    | _ -> None)
              end
        in
        Ok
          {
            au_key = key;
            au_owner = owner;
            au_private = shape;
            au_token = au_source.au_token;
            au_source;
            au_procedure = au_procedure au_source f;
            au_inputs = shape.inputs;
            au_result = shape.result;
            au_ghost_outputs = shape.ghost_outputs;
            au_implicit = shape.implicit;
          })
  in
  let proof_support = { proof_support with atomic_updates } in
  let atomic_predicates = atomic_predicates (context_atomic None atomic_updates) in
  let preds = preds @ atomic_predicates in
  let spec_funcs =
    spec_funcs @ List.map atomic_predicates ~f:(fun (key, _) -> (key, key))
  in
  let lemma_declarations =
    List.filter source.proof ~f:(function S.Proof_lemma _ -> true | _ -> false)
    @ List.filter_map scoped_proofs.bindings ~f:scoped_lemma
  in
  let* () =
    check_lemma_recursion lemma_declarations ~resolve:(fun at q ->
        let binding =
          List.find scoped_proofs.bindings ~f:(fun binding ->
              Poly.equal binding.entry.name.pid_loc at)
        in
        let scope = Option.map binding ~f:(fun binding -> binding.entry.scope) in
        let environment =
          Option.value_map binding ~default:source.env ~f:(fun binding ->
              binding.environment)
        in
        let key =
          Option.value
            (Proof_bindings.resolve scoped_proofs ~scope ~environment q)
            ~default:(qualid_key q)
        in
        Option.value (Proof_bindings.canonical_key scoped_proofs key) ~default:key)
  in
  let* all_proof_lemmas =
    all lemma_declarations ~f:(function
      | S.Proof_lemma { lemma_name; lemma_params; lemma_returns; _ } ->
          let ocaml_env = declaration_environment lemma_name.pid_str in
          let types_of ps =
            all ps ~f:(fun (id, ty) -> Source.ocaml_type ocaml_env ~at:id.S.pid_loc ty)
          in
          let* implicit = implicit_parameter_count ~kind:"lemma" lemma_params in
          let lemma_implicit_count = Option.value implicit ~default:0 in
          let* lemma_inputs = types_of lemma_params in
          let* lemma_outputs = types_of lemma_returns in
          if
            List.Assoc.mem spec_funcs lemma_name.pid_str ~equal:String.equal
            || List.exists funcs ~f:(fun f ->
                String.equal f.raven_name lemma_name.pid_str)
          then
            error lemma_name.pid_loc
              (Printf.sprintf "Name %s is already declared" lemma_name.pid_str)
          else
            Ok
              ( lemma_name.pid_str,
                {
                  lemma_raven = lemma_name.pid_str;
                  lemma_constant = false;
                  lemma_inputs;
                  lemma_implicit_count;
                  lemma_outputs;
                } )
      | _ -> error Location.none "Expected a lemma declaration")
  in
  let* () =
    match List.find_a_dup (List.map all_proof_lemmas ~f:fst) ~compare:String.compare with
    | None -> Ok ()
    | Some x -> error Location.none (Printf.sprintf "Duplicate lemma %s" x)
  in
  let proof_lemmas =
    List.filter all_proof_lemmas ~f:(fun (key, _) -> Option.is_none (scoped_binding key))
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        match binding.kind with
        | Lemma (S.Proof_lemma declaration) when binding.exported ->
            let inputs, outputs =
              List.split_n binding.public_types (List.length declaration.lemma_params)
            in
            let signature =
              List.Assoc.find_exn all_proof_lemmas binding.backend ~equal:String.equal
            in
            Some
              ( binding.public_key,
                { signature with lemma_inputs = inputs; lemma_outputs = outputs } )
        | _ -> None)
  in
  let lemma_context ?at scope =
    let owners = context_owners at in
    let environment =
      Option.value_map scope ~default:source.env ~f:(fun scope ->
          Source.annotation_env source scope.Proof_scopes.environment)
    in
    let project = Proof_bindings.context_type scoped_proofs ~environment in
    let proof_lemmas =
      List.filter_map (Proof_bindings.local_exports scoped_proofs ~scope)
        ~f:(fun binding ->
          match binding.kind with
          | Lemma (S.Proof_lemma declaration) ->
              let inputs, outputs =
                List.split_n binding.public_types (List.length declaration.lemma_params)
              in
              let signature =
                List.Assoc.find_exn all_proof_lemmas binding.backend ~equal:String.equal
              in
              Some
                ( binding.public_key,
                  { signature with lemma_inputs = inputs; lemma_outputs = outputs } )
          | _ -> None)
      @ proof_lemmas
    in
    let proof_lemmas =
      List.map proof_lemmas ~f:(fun (key, signature) ->
          ( key,
            {
              signature with
              lemma_inputs = List.map signature.lemma_inputs ~f:project;
              lemma_outputs = List.map signature.lemma_outputs ~f:project;
            } ))
    in
    let proof_lemmas =
      List.filter_map scoped_proofs.applications ~f:(fun view ->
          if not (Proof_bindings.application_visible ~owners scoped_proofs ~scope view)
          then None
          else
            Option.map
              (List.Assoc.find all_proof_lemmas view.source.backend ~equal:String.equal)
              ~f:(fun signature ->
                let inputs, outputs =
                  List.split_n view.types (List.length signature.lemma_inputs)
                in
                ( view.key,
                  {
                    signature with
                    lemma_raven = view.backend;
                    lemma_inputs = List.map inputs ~f:project;
                    lemma_outputs = List.map outputs ~f:project;
                  } )))
      @ proof_lemmas
    in
    List.filter_map (Proof_bindings.private_bindings scoped_proofs ~scope)
      ~f:(fun binding ->
        Option.map (List.Assoc.find all_proof_lemmas binding.backend ~equal:String.equal)
          ~f:(fun signature ->
            ( binding.backend,
              {
                signature with
                lemma_raven =
                  Option.value (definition_target binding) ~default:signature.lemma_raven;
              } )))
    @ proof_lemmas
  in
  (* The views, with their values, and their ghost fields, on the structures. *)
  let views =
    List.filter_map predicates ~f:(fun (_, p, def, types) ->
        match def with
        | View { value } -> Some (p, value, types)
        | Body _ | Direct_invariant _ | Invariant _ -> None)
  in
  let* view_fields =
    all views ~f:(fun ((p : S.predicate), _, param_types) ->
        let at = p.pred_name.pid_loc in
        let structure = List.hd_exn param_types in
        let* anchor =
          match Option.map (anchor types structure) ~f:fst with
          | Some anchor -> Ok anchor
          | None ->
              error at
                "The structure of a view is a reference: an atomic, a ref or a record \
                 with a mutable field"
        in
        let* typ = Datatypes.typ types ~at (List.last_exn param_types) in
        let field =
          Module_context.member
            (declaration_context p.pred_name.pid_str)
            (view_field p.pred_name.pid_str)
        in
        Ok (anchor, (field, typ, None)))
  in
  let resolve_function ~environment (id : S.id) =
    match Source.value_path environment (S.Qid id) with
    | Some path ->
        let path = Proof_bindings.canonical_owner scoped_proofs path in
        begin match
          List.find funcs ~f:(fun f -> List.mem f.paths path ~equal:Path.same)
        with
        | Some f -> Ok f.id
        | None ->
            begin match
              List.find_map generic_proofs ~f:(fun plan ->
                  Option.bind (Source.scoped_value_name plan.Generic_proofs.scope path)
                    ~f:(fun member ->
                      List.Assoc.find plan.group.representative.members member
                        ~equal:String.equal))
            with
            | Some id -> Ok id
            | None ->
                error id.pid_loc
                  (Printf.sprintf "There is no implementation function %s" id.pid_str)
            end
        end
    | None ->
        error id.pid_loc
          (Printf.sprintf "There is no implementation function %s" id.pid_str)
  in
  (* The structures with a state, and their histories, allocated empty. *)
  let action_declarations =
    List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
        match entry.Proof_scopes.declaration with
        | S.Proof_action declaration ->
            let scope = Option.some_if (Option.is_some entry.scope.owner) entry.scope in
            let backend =
              Option.value_map
                (List.find scoped_proofs.bindings ~f:(fun binding ->
                     Ident.same binding.entry.id entry.id))
                ~default:declaration.action_name.pid_str
                ~f:(fun binding -> binding.backend)
            in
            Some
              ( scope,
                Source.annotation_env source entry.scope.environment,
                backend,
                entry.declaration )
        | _ -> None)
  in
  let* actions =
    all action_declarations ~f:(fun (scope, environment, backend, proof) ->
        match proof with
        | S.Proof_action declaration ->
            let* linearizes =
              all declaration.action_linearizes ~f:(resolve_function ~environment)
            in
            let helps =
              Option.bind declaration.action_helps ~f:(fun (field, key, result) ->
                  match field.term_desc with
                  | Tfield (_, Qid field) -> Some (field.pid_str, key, result)
                  | _ -> None)
            in
            Ok
              ( scope,
                {
                  action = backend;
                  params = List.map declaration.action_params ~f:(fun id -> id.S.pid_str);
                  step =
                    Option.map declaration.action_step ~f:(fun (op, args) ->
                        (op.pid_str, args));
                  state = declaration.action_state.pid_str;
                  update =
                    List.map declaration.action_update ~f:(fun (field, term) ->
                        (field.S.pid_str, term));
                  linearizes;
                  helps;
                  action_at = declaration.action_name.pid_loc;
                } )
        | _ -> error Location.none "Expected an action declaration")
  in
  let same_scope a b =
    Option.equal
      (fun a b -> Option.equal Path.same a.Proof_scopes.owner b.Proof_scopes.owner)
      a b
  in
  let* structures =
    all
      (List.filter_map predicates ~f:(fun (at, p, def, param_types) ->
           match def with
           | Invariant { state; fields; body; field_environment; field_scope } ->
               Some
                 (at, p, state, fields, body, param_types, field_environment, field_scope)
           | Body _ | Direct_invariant _ | View _ -> None))
      ~f:(fun
          ( at,
            (p : S.predicate),
            state,
            state_fields,
            body,
            param_types,
            field_environment,
            field_scope )
        ->
        let scope = declaration_scope p.pred_name.pid_str in
        let environment = declaration_environment p.pred_name.pid_str in
        let declaration_predicates, declaration_functions, declaration_support =
          proof_context_for ~preds ~spec_funcs ~proof_support p.pred_name.pid_str
        in
        let context =
          { declaration_predicates; declaration_functions; declaration_support }
        in
        let field_type term =
          let* ty = Source.ocaml_type field_environment ~at term in
          let private_state =
            match (field_scope, scope) with
            | None, _ -> true
            | Some owner, Some caller ->
                Option.is_some
                  (Proof_bindings.drop_prefix owner.namespace caller.namespace)
            | Some _, None -> false
          in
          Ok
            (if private_state then ty
             else
               Proof_bindings.context_type scoped_proofs ~environment
                 (Proof_bindings.public_type scoped_proofs ty))
        in
        let actions =
          List.filter_map actions ~f:(fun (owner, action) ->
              Option.some_if
                (same_scope owner scope
                && String.equal action.state state
                && List.for_all action.update ~f:(fun (field, _) ->
                    List.exists state_fields ~f:(fun sf ->
                        String.equal sf.S.sf_name.pid_str field)))
                action)
        in
        (* The key type of a field of pending calls. *)
        let pending_key t =
          match Datatypes.desc types t with
          | Tconstr (path, [ key ], _) when Path.same path source.pending -> Some key
          | _ -> None
        in
        let* fields =
          all state_fields ~f:(fun (sf : S.state_field) ->
              let* t = field_type sf.sf_type in
              let raven = state ^ "_" ^ sf.sf_name.pid_str in
              match pending_key t with
              | Some _ ->
                  (* The registrations, which only grow. *)
                  Ok
                    ( sf.sf_name.pid_str,
                      raven,
                      R.Type.fin_set ~loc:(loc at) (R.Type.ref ~loc:(loc at)),
                      t,
                      true )
              | None ->
                  let* typ = Datatypes.typ types ~at t in
                  Ok (sf.sf_name.pid_str, raven, typ, t, sf.sf_grows))
        in
        let* pendings =
          all
            (List.filter_map state_fields ~f:(fun (sf : S.state_field) ->
                 match field_type sf.sf_type with
                 | Ok t -> Option.map (pending_key t) ~f:(fun key -> (sf, key))
                 | Error _ -> None))
            ~f:(fun ((sf : S.state_field), key) ->
              let field = sf.sf_name.pid_str in
              let* helped =
                match sf.sf_helps with
                | Some f ->
                    resolve_function ~environment:field_environment
                      (S.mk_id ~loc:sf.sf_name.pid_loc f)
                | None ->
                    error sf.sf_name.pid_loc
                      "A field of pending calls names the function whose calls wait, as \
                       [@helps is_empty]"
              in
              let* helping =
                match
                  List.filter_map actions ~f:(fun a ->
                      match a.helps with
                      | Some (f, k, v) when String.equal f field -> Some (a.state, k, v)
                      | _ -> None)
                with
                | [ helping ] -> Ok helping
                | [] ->
                    error sf.sf_name.pid_loc
                      "No action helps the calls of this field: give one as [helps s.f \
                       on key with result]"
                | _ :: _ :: _ ->
                    unsupported sf.sf_name.pid_loc
                      "Helping the calls of a field by several actions"
              in
              Ok
                {
                  pending_field = field;
                  pending_on = state ^ "_" ^ field ^ "_on";
                  key_type = key;
                  helped;
                  helping;
                })
        in
        let chains =
          List.dedup_and_sort ~compare:String.compare
            (List.filter_map (conjuncts body) ~f:(fun t ->
                 Option.map (chain_of ~state t) ~f:(fun (_, _, field, _) -> field)))
        in
        Ok
          {
            context;
            scope;
            environment;
            invariant = p.pred_name.pid_str;
            backend =
              Module_context.member
                (declaration_context p.pred_name.pid_str)
                p.pred_name.pid_str;
            state;
            fields;
            chains = List.map chains ~f:(fun f -> (f, state ^ "_" ^ f ^ "_index"));
            actions;
            pendings;
            held =
              List.filter_map (conjuncts body) ~f:(fun t ->
                  match spine t [] with
                  | ( { term_desc = Tvar (Qid { pid_str = "own"; _ }); _ },
                      [ location; value ] ) ->
                      begin match spine value [] with
                      | ( { term_desc = Tvar (Qid { pid_str = "([])"; _ }); _ },
                          [
                            {
                              term_desc =
                                Tfield
                                  ( { term_desc = Tvar (Qid { pid_str = x; _ }); _ },
                                    Qid { pid_str = f; _ } );
                              _;
                            };
                            position;
                          ] )
                        when String.equal x state && List.mem chains f ~equal:String.equal
                        ->
                          Some (location, f, position)
                      | _ -> None
                      end
                  | _ -> None);
            params =
              List.zip_exn
                (List.map p.pred_params ~f:(fun (x, _) -> x.S.pid_str))
                (List.take param_types (List.length p.pred_params));
            structure_type = List.hd_exn param_types;
            views =
              List.filter_map views ~f:(fun (view, value, view_types) ->
                  let params = List.drop_last_exn view_types in
                  let state_names =
                    List.filter_map (term_references [] value) ~f:(function
                      | S.Qid id
                        when (not
                                (List.exists view.pred_params ~f:(fun (parameter, _) ->
                                     String.equal parameter.S.pid_str id.pid_str)))
                             && List.exists predicates
                                  ~f:(fun (_, predicate, definition, _) ->
                                    same_scope scope
                                      (declaration_scope predicate.S.pred_name.pid_str)
                                    &&
                                    match definition with
                                    | Invariant { state; _ } ->
                                        String.equal state id.pid_str
                                    | _ -> false) ->
                          Some id.pid_str
                      | Qid _ | Qdot _ -> None)
                  in
                  Option.some_if
                    (same_scope scope (declaration_scope view.pred_name.pid_str)
                    && List.length params = List.length param_types
                    && Ctype.is_equal environment false params param_types
                    && (List.is_empty state_names
                       || List.mem state_names state ~equal:String.equal))
                    (view, value));
            at;
          })
  in
  let* _ =
    all actions ~f:(fun (_, action) ->
        match
          List.filter structures ~f:(fun st ->
              List.exists st.actions ~f:(fun a -> String.equal a.action action.action))
        with
        | [ _ ] -> Ok ()
        | [] -> error action.action_at "No stateful invariant matches this action"
        | _ ->
            error action.action_at
              "Several stateful invariants match this action: use distinct state binders")
  in
  let* _ =
    all views ~f:(fun (view, _, _) ->
        match
          List.filter structures ~f:(fun st ->
              List.exists st.views ~f:(fun (p, _) ->
                  String.equal p.S.pred_name.pid_str view.S.pred_name.pid_str))
        with
        | [ _ ] -> Ok ()
        | [] -> error view.pred_name.pid_loc "No stateful invariant matches this view"
        | _ ->
            error view.pred_name.pid_loc
              "Several stateful invariants match this view: use distinct state binders")
  in
  let* application_identities =
    all generics ~f:(fun group ->
        let* identities =
          all group.Generic_modules.applications ~f:(fun application ->
              let* identity =
                Signature_contract.compiler ~at:application.source.argument.site.item_loc
                  (fun () ->
                    Env.normalize_module_path None source.env application.source.identity)
              in
              Ok (application, identity))
        in
        Ok (group.name, identities))
  in
  let canonical_application group application =
    let identities =
      List.Assoc.find_exn application_identities group.Generic_modules.name
        ~equal:String.equal
    in
    let identity = List.Assoc.find_exn identities application ~equal:phys_equal in
    fst (List.find_exn identities ~f:(fun (_, other) -> Path.same other identity))
  in
  let application_aliases =
    List.concat_map generics ~f:(fun group ->
        List.filter_map group.Generic_modules.applications ~f:(fun application ->
            let canonical = canonical_application group application in
            Option.some_if
              (not (phys_equal canonical application))
              (application.name, canonical.name)))
  in
  let canonical_backend backend =
    Option.value
      (List.find_map application_aliases ~f:(fun (alias, target) ->
           Option.map
             (String.chop_prefix backend ~prefix:(alias ^ "."))
             ~f:(fun suffix -> target ^ "." ^ suffix)))
      ~default:backend
  in
  let declared_structures = structures in
  let* application_structures =
    all
      (List.filter_map scoped_proofs.applications ~f:(fun view ->
           Option.map
             (List.find structures ~f:(fun st ->
                  String.equal st.invariant view.source.backend))
             ~f:(fun st -> (view, st))))
      ~f:(fun (view, st) ->
        let plan = Option.value_exn (proof_worker st.invariant) in
        let project = view.Proof_bindings.project_type in
        let rebase text =
          Option.value_map
            (String.chop_prefix text ~prefix:(plan.group.name ^ "."))
            ~default:text
            ~f:(fun suffix ->
              let prefix = (Qualified_name.of_string view.backend).path in
              canonical_backend (String.concat ~sep:"." (prefix @ [ suffix ])))
        in
        let instance =
          List.find_exn plan.group.applications ~f:(fun instance ->
              String.equal view.backend
                (instance.Generic_modules.name ^ "." ^ view.source.backend))
        in
        let projection =
          Generic_proofs.application_projection source plan instance.source view.path
        in
        let project_path = Subst.module_path projection in
        let project_atomic_source (au : Source.proof_au) =
          {
            au with
            au_scope = Option.map au.au_scope ~f:project_path;
            au_path = project_path au.au_path;
            au_operation_path = project_path au.au_operation_path;
            au_operation_type = project au.au_operation_type;
            au_token = project au.au_token;
            au_token_path = project_path au.au_token_path;
            au_token_paths = List.map au.au_token_paths ~f:project_path;
          }
        in
        let project_lemma signature =
          {
            signature with
            lemma_raven = rebase signature.lemma_raven;
            lemma_inputs = List.map signature.lemma_inputs ~f:project;
            lemma_outputs = List.map signature.lemma_outputs ~f:project;
          }
        in
        let support = st.context.declaration_support in
        let support =
          {
            support with
            runtime_functions =
              Path_bindings.of_list
                (List.map support.runtime_functions.entries ~f:(fun (path, target) ->
                     ( project_path path,
                       Qualified_name.of_string (rebase (Qualified_name.to_string target))
                     )));
            predicate_views =
              Path_bindings.of_list
                (List.map support.predicate_views.entries ~f:(fun (path, key) ->
                     (project_path path, rebase key)));
            public_types = List.map support.public_types ~f:project_path;
            library_paths =
              Path_bindings.of_list
                (List.map support.library_paths.entries ~f:(fun (path, names) ->
                     (project_path path, names)));
            resources =
              List.map support.resources ~f:(fun resource ->
                  {
                    resource with
                    resource_backend = rebase resource.Source.resource_backend;
                    resource_path = project_path resource.resource_path;
                    resource_type = project resource.resource_type;
                    resource_operations =
                      List.map resource.resource_operations
                        ~f:(fun (name, inputs, output) ->
                          (name, List.map inputs ~f:project, project output));
                  });
            ghost_fields =
              List.map support.ghost_fields ~f:(fun field ->
                  {
                    field with
                    field_backend = rebase field.Source.field_backend;
                    field_scope = Option.map field.field_scope ~f:project_path;
                    field_path = project_path field.field_path;
                    field_owner = project field.field_owner;
                    field_value = project field.field_value;
                    field_resource = Option.map field.field_resource ~f:project_path;
                  });
            atomic_updates =
              List.map support.atomic_updates ~f:(fun signature ->
                  {
                    signature with
                    au_owner = Option.map signature.au_owner ~f:project_path;
                    au_private =
                      {
                        inputs = List.map signature.au_private.inputs ~f:project;
                        result = project signature.au_private.result;
                        ghost_outputs =
                          List.map signature.au_private.ghost_outputs ~f:project;
                        implicit = List.map signature.au_private.implicit ~f:project;
                      };
                    au_token = project signature.au_token;
                    au_source = project_atomic_source signature.au_source;
                    au_procedure = rebase signature.au_procedure;
                    au_inputs = List.map signature.au_inputs ~f:project;
                    au_result = project signature.au_result;
                    au_ghost_outputs = List.map signature.au_ghost_outputs ~f:project;
                    au_implicit = List.map signature.au_implicit ~f:project;
                  });
            logical_functions =
              List.map support.logical_functions ~f:(fun (key, signature) ->
                  (key, project_lemma signature));
          }
        in
        let* fields =
          all st.fields ~f:(fun (field, raven, typ, ty, grows) ->
              let ty = project ty in
              let* typ =
                if
                  List.exists st.pendings ~f:(fun pending ->
                      String.equal pending.pending_field field)
                then Ok typ
                else Datatypes.typ types ~at:st.at ty
              in
              Ok (field, raven, typ, ty, grows))
        in
        let views =
          List.filter_map st.views ~f:(fun (predicate, value) ->
              Option.map
                (List.find scoped_proofs.applications ~f:(fun other ->
                     Path.same other.path view.path
                     && String.equal other.source.backend predicate.S.pred_name.pid_str))
                ~f:(fun other ->
                  ( {
                      predicate with
                      pred_name = { predicate.pred_name with pid_str = other.key };
                    },
                    value )))
        in
        let member_id id =
          Option.value_map
            (List.find plan.group.representative.members ~f:(fun (_, original) ->
                 Ident.same original id))
            ~default:id
            ~f:(fun (name, _) ->
              Option.value
                (List.Assoc.find instance.source.members name ~equal:String.equal)
                ~default:id)
        in
        let application_substitution =
          Generic_proofs.application_substitution plan instance.source
        in
        let environment =
          List.fold (Generic_proofs.source_parameters plan) ~init:view.environment
            ~f:(fun environment parameter ->
              let argument =
                Subst.module_path application_substitution (Path.Pident parameter)
              in
              Env.add_module ~noalias:false parameter Types.Mp_present
                (Types.Mty_alias argument) environment)
        in
        Ok
          {
            st with
            invariant = canonical_backend view.backend;
            backend = canonical_backend view.backend;
            fields;
            views;
            environment;
            context =
              {
                declaration_predicates =
                  List.map st.context.declaration_predicates
                    ~f:(fun (key, (target, tys)) ->
                      (key, (rebase target, List.map tys ~f:project)));
                declaration_functions =
                  List.map st.context.declaration_functions ~f:(fun (key, target) ->
                      (key, rebase target));
                declaration_support = support;
              };
            params = List.map st.params ~f:(fun (key, ty) -> (key, project ty));
            structure_type = project st.structure_type;
            actions =
              List.map st.actions ~f:(fun action ->
                  { action with linearizes = List.map action.linearizes ~f:member_id });
            pendings =
              List.map st.pendings ~f:(fun pending ->
                  {
                    pending with
                    key_type = project pending.key_type;
                    helped = member_id pending.helped;
                  });
          })
  in
  let application_structures =
    List.dedup_and_sort application_structures ~compare:(fun left right ->
        String.compare left.backend right.backend)
  in
  let* structure_member_lists =
    all structures ~f:(fun st ->
        let* members = structure_members types st ~at:st.at in
        Ok (st, members))
  in
  let history_fields =
    List.filter_map structures ~f:(fun st ->
        Option.some_if (has_history st)
          (let l = R.Loc.none in
           let qn m x = qualified_name ~loc:l (m ^ "." ^ x) in
           ( Option.value_map (anchor types st.structure_type) ~default:"" ~f:fst,
             ( member_name st "history",
               R.Type.named ~loc:l (qualified_name ~loc:l (module_name st "history")) [],
               Some
                 (R.Expr.call ~loc:l
                    (qn (module_name st "history") "full")
                    [
                      R.Expr.call ~loc:l
                        (qn (module_name st "states") "set")
                        [ R.Expr.set ~loc:l [] ];
                    ]) ) )))
  in
  let view_fields = view_fields @ history_fields in
  let destination_of_group = function
    | None -> Module_context.Flat
    | Some group -> Module_context.Worker group
  in
  let owner_destination name = (declaration_context name).destination in
  let same_group left right =
    Module_context.same_destination (destination_of_group left)
      (destination_of_group right)
  in
  let visible_state group name =
    match owner_destination name with
    | Module_context.Flat -> true
    | destination ->
        Module_context.same_destination destination (destination_of_group group)
  in
  let field_group field =
    List.find generics ~f:(fun group ->
        String.is_prefix field ~prefix:(group.Generic_modules.name ^ "."))
  in
  let make_shared group =
    let persistent =
      List.filter_map predicates ~f:(fun (at, p, def, _) ->
          match def with
          | (Direct_invariant _ | Invariant _)
            when visible_state group p.pred_name.pid_str ->
              Some
                ( Module_context.member
                    (declaration_context p.pred_name.pid_str)
                    p.pred_name.pid_str,
                  at )
          | _ -> None)
    in
    let selected_views =
      List.filter views ~f:(fun (p, _, _) -> visible_state group p.S.pred_name.pid_str)
    in
    let view_names =
      List.map selected_views ~f:(fun (p, _, _) ->
          let key = p.S.pred_name.pid_str in
          let field = Module_context.member (declaration_context key) (view_field key) in
          (key, field))
    in
    let persistent, view_names =
      match group with
      | Some _ -> (persistent, view_names)
      | None ->
          List.fold scoped_proofs.applications ~init:(persistent, view_names)
            ~f:(fun (persistent, views) view ->
              match view.source.kind with
              | Predicate (p, View _) ->
                  let backend = Qualified_name.of_string view.backend in
                  ( persistent,
                    ( view.key,
                      canonical_backend
                        (String.concat ~sep:"."
                           (backend.path @ [ view_field backend.name ])) )
                    :: views )
              | Predicate (p, _) when p.pred_persistent ->
                  ( (canonical_backend view.backend, p.pred_name.pid_loc) :: persistent,
                    views )
              | _ -> (persistent, views))
    in
    let selected_fields =
      List.filter view_fields ~f:(fun (_, (field, _, _)) ->
          match field_group field with
          | None -> true
          | Some owner -> Option.exists group ~f:(phys_equal owner))
    in
    {
      persistent;
      member_aliases = (if Option.is_none group then application_aliases else []);
      views = view_names;
      structures =
        (List.filter_map declared_structures ~f:(fun st ->
             Option.some_if
               (visible_state group st.invariant)
               { st with invariant = st.backend })
        @ if Option.is_none group then application_structures else []);
      dynamic_indices = false;
      anchors =
        List.map
          (List.dedup_and_sort (List.map selected_fields ~f:fst) ~compare:String.compare)
          ~f:(fun anchor ->
            ( anchor,
              List.filter_map selected_fields ~f:(fun (owner, field) ->
                  Option.some_if (String.equal owner anchor) field) ));
    }
  in
  let shared = make_shared None in
  let generic_shared =
    List.map generics ~f:(fun group ->
        (group.Generic_modules.name, make_shared (Some group)))
  in
  let shared_for_destination = function
    | Module_context.Flat -> shared
    | Module_context.Worker group ->
        List.Assoc.find_exn generic_shared group.Generic_modules.name ~equal:String.equal
  in
  let shared_for_proof name = shared_for_destination (owner_destination name) in
  let body_shared f = shared_for_destination (body_module_context f).destination in
  let state_members group lists =
    List.concat_map lists ~f:(fun (st, members) ->
        Option.some_if
          (Module_context.same_destination
             (owner_destination st.invariant)
             (destination_of_group group))
          members
        |> Option.value ~default:[])
  in
  let past_structures ?(symbolic = false) (f : func) =
    let scope = Proof_bindings.scope_for_location scoped_proofs f.loc in
    let context = proof_context scope preds spec_funcs proof_support in
    let owner = body_module_context f in
    let predicates, _, support =
      module_context owner ~projection:owner.projection context
    in
    let selected_shared = if symbolic then body_shared f else shared in
    let predicates =
      match (symbolic, body_owner f) with
      | false, Some (group, _) ->
          let _, application, _ =
            Option.value_exn (Generic_modules.member generics f.id)
          in
          let target = (canonical_application group application).name in
          List.map predicates ~f:(fun (key, (backend, types)) ->
              let backend =
                Option.value_map
                  (String.chop_prefix backend ~prefix:(group.name ^ "."))
                  ~default:backend
                  ~f:(fun suffix -> target ^ "." ^ suffix)
              in
              (key, (backend, types)))
      | _ -> predicates
    in
    let structures = selected_shared.structures in
    let references =
      Option.value_map f.contract ~default:[] ~f:(fun c ->
          List.concat_map (c.requires @ c.ensures) ~f:(term_references []))
    in
    let keys =
      List.filter_map references ~f:(fun q ->
          let key =
            match (support.proof_key f.environment q, q) with
            | Some key, _ -> Some key
            | None, S.Qid id -> Some id.pid_str
            | None, Qdot _ -> None
          in
          Option.map key ~f:(fun key ->
              Option.value_map (List.Assoc.find predicates key ~equal:String.equal)
                ~default:key ~f:(fun (backend, _) ->
                  canonical_member selected_shared backend)))
    in
    let selected =
      List.filter structures ~f:(fun st ->
          List.mem keys st.invariant ~equal:String.equal
          || List.exists st.views ~f:(fun (p, _) ->
              List.mem keys
                (Option.value_map
                   (List.Assoc.find predicates p.S.pred_name.pid_str ~equal:String.equal)
                   ~default:p.pred_name.pid_str ~f:(fun (backend, _) ->
                     canonical_member selected_shared backend))
                ~equal:String.equal))
    in
    if not (List.is_empty selected) then selected
    else
      let namespace =
        Option.value_map scope ~default:[] ~f:(fun s -> s.Proof_scopes.namespace)
      in
      let owner st =
        Option.value_map st.scope ~default:[] ~f:(fun s -> s.Proof_scopes.namespace)
      in
      let visible =
        List.filter structures ~f:(fun st ->
            Option.is_some (Proof_bindings.drop_prefix (owner st) namespace))
      in
      List.filter visible ~f:(fun st ->
          not
            (List.exists visible ~f:(fun other ->
                 String.equal st.state other.state
                 && List.length (owner other) > List.length (owner st))))
  in
  (* The facts about earlier states in contracts, by the parameter they are about. *)
  let* pasts =
    all funcs ~f:(fun f ->
        let structures = past_structures f in
        let* _ =
          all
            (Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires @ c.ensures))
            ~f:(fun term ->
              if
                List.count structures ~f:(fun st -> Option.is_some (past_of [ st ] term))
                > 1
              then
                error term.term_loc
                  "Several stateful invariants match this past fact: use distinct state \
                   binders"
              else Ok ())
        in
        let clauses select =
          Option.value_map f.contract ~default:[] ~f:select
          |> List.filter_map ~f:(past_of structures)
        in
        let* _, names =
          contract_names f
            (Option.bind f.contract ~f:(fun c -> c.header))
            (List.length f.params)
        in
        let* required =
          all
            (clauses (fun c -> c.requires))
            ~f:(fun p ->
              let position =
                match p.element.term_desc with
                | Tvar (Qid { pid_str = x; _ }) ->
                    List.findi names ~f:(fun _ n -> Option.equal String.equal n (Some x))
                | _ -> None
              in
              match position with
              | Some (i, _) -> Ok (p.inv, p.field, i)
              | None ->
                  unsupported p.element.term_loc
                    "A fact about an earlier state other than of a parameter,")
        in
        Ok
          ( (proc_name f, required),
            ( proc_name f,
              List.map
                (clauses (fun c -> c.ensures))
                ~f:(fun p -> (p.inv, p.field, entry_of_args types f names p.element)) ) ))
  in
  let pasts, past_returns = List.unzip pasts in
  let body_past_name f inv =
    match body_owner f with
    | None -> inv
    | Some (group, _) ->
        let _, application, _ = Option.value_exn (Generic_modules.member generics f.id) in
        let prefix = (canonical_application group application).name in
        Option.value_map
          (String.chop_prefix inv ~prefix:(prefix ^ "."))
          ~default:inv
          ~f:(fun suffix -> group.name ^ "." ^ suffix)
  in
  let with_body_pasts entries project =
    entries
    @ List.filter_map funcs ~f:(fun f ->
        match body_owner f with
        | Some (_, true) ->
            Option.map
              (List.Assoc.find entries (proc_name f) ~equal:String.equal)
              ~f:(fun value -> (body_proc_name f, project f value))
        | _ -> None)
  in
  let pasts =
    with_body_pasts pasts (fun f clauses ->
        List.map clauses ~f:(fun (inv, field, position) ->
            (body_past_name f inv, field, position)))
  in
  let past_returns =
    with_body_pasts past_returns (fun f clauses ->
        List.map clauses ~f:(fun (inv, field, element) ->
            (body_past_name f inv, field, element)))
  in
  (* For each ghost parameter, a parameter that a precondition makes a field of it. *)
  let* ghost_args =
    all funcs ~f:(fun f ->
        let* _, names =
          contract_names f
            (Option.bind f.contract ~f:(fun c -> c.header))
            (List.length f.params)
        in
        let equations =
          field_equations
            (Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires))
        in
        Ok
          ( proc_name f,
            List.map (ghost_params f) ~f:(fun (g, _) ->
                List.find_map equations ~f:(fun (x, field, h) ->
                    if not (String.equal h g.S.pid_str) then None
                    else
                      Option.map
                        (List.findi names ~f:(fun _ n ->
                             Option.equal String.equal n (Some x)))
                        ~f:(fun (i, _) -> (i, field)))) ))
  in
  let ghost_args = with_body_names ghost_args in
  (* Each library's module, trusted: its abstract predicates, and its values, as functions
     without arguments, and functions, as procedures with their contracts. *)
  let* library_modules =
    all libraries ~f:(fun (lib : Library_modules.t) ->
        let l = loc Location.none in
        let* environment = Library_modules.environment source lib in
        let own_preds =
          List.filter_map library_preds ~f:(fun ((lib' : Library_modules.t), p, types) ->
              Option.some_if
                (String.equal lib'.library_name lib.library_name)
                ( p.pred_name.pid_str,
                  (lib.library_name ^ "." ^ p.pred_name.pid_str, types) ))
        in
        (* In the library's contracts, its predicates go by their own names. *)
        let own_inputs =
          List.filter_map own_preds ~f:(fun (local, (qualified, _)) ->
              Option.map
                (List.Assoc.find proof_support.predicate_inputs qualified
                   ~equal:String.equal) ~f:(fun inputs -> (local, inputs)))
        in
        let ctx =
          scoped_contract_context types ~refs ~primitives ~shared ~environment
            ~proof_support ~preds ~spec_funcs ~own_preds ~own_inputs origins
        in
        let* pred_members =
          all
            (List.filter library_preds ~f:(fun ((lib' : Library_modules.t), _, _) ->
                 String.equal lib'.library_name lib.library_name))
            ~f:(fun (_, (p : S.predicate), param_types) ->
              let* params =
                all (List.zip_exn p.pred_params param_types) ~f:(fun ((x, _), t) ->
                    let* typ = Datatypes.typ types ~at:x.S.pid_loc t in
                    Ok (t, R.Var.make ~loc:l (ident ~loc:l x.pid_str) typ))
              in
              (* Libraries share the program's predicate output convention. *)
              let* outputs = predicate_output_count types p param_types in
              let inputs, outputs = List.split_n params (List.length params - outputs) in
              let kind = if p.pred_persistent then R.Callable.Inv else R.Callable.Pred in
              Ok
                (R.Member.free
                   (R.Member.callable
                      (R.Callable.func ~loc:l ~kind ~formals:(List.map inputs ~f:snd)
                         ~returns:(List.map outputs ~f:snd)
                         (ident ~loc:l p.pred_name.pid_str)
                         None))))
        in
        let* contracts = interface_contracts lib.library in
        let* value_members =
          all lib.library.signature ~f:(fun (item : Parsetree.signature_item) ->
              match item.psig_desc with
              | Psig_value vd ->
                  let at = vd.pval_loc in
                  let x = vd.pval_name.txt in
                  let value = Env.find_value (Pdot (lib.library_path, x)) source.env in
                  let rec arrows (t : Types.type_expr) =
                    match Types.get_desc t with
                    | Tarrow (Nolabel, a, r, _) ->
                        let args, result = arrows r in
                        (Datatypes.expand types a :: args, result)
                    | Tpoly (t, []) -> arrows t
                    | _ -> ([], t)
                  in
                  let args, result = arrows value.val_type in
                  let contract =
                    Option.map (List.Assoc.find contracts x ~equal:String.equal) ~f:fst
                  in
                  let* member = library_function ctx ~at ~name:x ~args ~result contract in
                  Ok [ R.Member.free (R.Member.callable member) ]
              | Psig_type _ | Psig_attribute _ -> Ok []
              | _ -> unsupported item.psig_loc "This item of a library's interface")
        in
        Ok
          (R.Member.module_ ~loc:l
             (ident ~loc:l lib.library_name)
             (pred_members @ List.concat value_members)))
  in
  let prepare_view_operation (view : checked_view) operation =
    let signature = operation.operation_signature in
    let* () =
      check_adapter_shape ~at:signature.site.item_loc operation.operation_contract
    in
    let* raw_resources =
      all view.view_resources ~f:(fun (formal, resource) ->
          let environment =
            Source.annotation_env source formal.Module_inventory.site.environment
          in
          let* ts =
            all formal.declaration.pred_params ~f:(fun (id, pty) ->
                Source.ocaml_type environment ~at:id.S.pid_loc pty)
          in
          Ok (formal.declaration, resource.resource_backend, ts))
    in
    let own_preds =
      List.map raw_resources ~f:(fun (p, target, ts) ->
          (p.S.pred_name.pid_str, (target, ts)))
    in
    let* own_inputs =
      all raw_resources ~f:(fun (p, _, ts) ->
          let* count = implicit_parameter_count ~kind:"predicate" p.S.pred_params in
          Ok
            (Option.map count ~f:(fun count ->
                 (p.pred_name.pid_str, List.length ts - count))))
    in
    let* environment =
      Source.realize_signature_ghost_environment source
        ~substitution:view.view_binding.parameter_substitution
        (List.map view.view_binding.expected.signature_ghost_modules
           ~f:(fun (_, formal) -> formal.Module_inventory.ghost_declaration))
        (Source.annotation_env source signature.site.environment)
    in
    let ctx =
      scoped_contract_context view.view_types ~refs ~primitives ~shared ~environment
        ~proof_support:{ proof_support with strict_source_types = true }
        ~preds ~spec_funcs ~own_preds ~own_inputs:(List.filter_opt own_inputs) origins
    in
    let predicates q =
      let env =
        {
          ctx;
          data = ctx.types;
          funcs = ctx.spec_funcs;
          vars = [];
          var_types = [];
          logical_definition = false;
        }
      in
      Option.map
        (List.Assoc.find ctx.preds (logical_key env q) ~equal:String.equal)
        ~f:snd
    in
    let* () =
      match operation.operation_contract with
      | None -> Ok ()
      | Some contract ->
          let* () = Signature_contract.lowerable source signature ~environment contract in
          Signature_contract.check ~logical_types:source.logical_types ~restricted:true
            ~predicates ~environment source signature contract
    in
    let args, result =
      Signature_contract.arguments signature.declaration.val_val.val_type
    in
    let* () =
      if List.is_empty args then
        unsupported signature.site.item_loc
          "A non-function value in a checked module signature"
      else Ok ()
    in
    let* expected =
      prepare_callable ~validate:true ctx ~at:signature.site.item_loc ~args ~result
        operation.operation_contract
    in
    Ok (ctx, args, result, expected)
  in
  let publication_members = ref [] in
  let publications = ref [] in
  let checked_prepared = ref [] in
  let* adapter_members =
    all checked_operations ~f:(fun operation ->
        let binding = operation.operation_binding in
        let view =
          List.find_exn checked_views ~f:(fun view ->
              phys_equal view.view_binding binding)
        in
        let signature = operation.operation_signature in
        let at = binding.site.item_loc in
        let member = signature.declaration.val_name.txt in
        let actual_path = Path.Pdot (binding.actual_path, member) in
        let* ctx, args, result, expected = prepare_view_operation view operation in
        let* actual, actual_contract, actual_projection, actual_at, actual_name =
          match List.Assoc.find !checked_prepared actual_path ~equal:Path.same with
          | Some info -> Ok info
          | None -> (
              match
                List.find funcs ~f:(fun f ->
                    List.mem f.paths actual_path ~equal:Path.same)
              with
              | Some f ->
                  let preds, spec_funcs, proof_support =
                    proof_context ~current_procedure:(proc_name f)
                      (Proof_bindings.scope_for_location scoped_proofs f.loc)
                      preds spec_funcs proof_support
                  in
                  let* () = check_adapter_shape ~at:f.loc f.contract in
                  let* () =
                    if
                      (is_pure f && logical_contract f.contract)
                      || (not (List.is_empty f.captured))
                      || Option.is_some f.role
                    then
                      unsupported at
                        "A pure or lifted operation in a checked module binding"
                    else Ok ()
                  in
                  let actual_ctx =
                    spec_context types ~refs ~primitives ~shared ~ocaml_env:f.environment
                      ~proof_support ~preds ~spec_funcs origins
                  in
                  let actual_args =
                    List.filter_map f.params ~f:(fun p ->
                        match p.Typedtree.fp_kind with
                        | Tparam_pat pat -> Some pat.pat_type
                        | _ -> None)
                  in
                  let* prepared =
                    prepare_callable actual_ctx ~at:f.loc ~args:actual_args
                      ~result:f.body.exp_type f.contract
                  in
                  let* () =
                    if
                      (not
                         (List.is_empty
                            (Option.value
                               (List.Assoc.find pasts (proc_name f) ~equal:String.equal)
                               ~default:[])))
                      || not
                           (List.is_empty
                              (Option.value
                                 (List.Assoc.find past_returns (proc_name f)
                                    ~equal:String.equal)
                                 ~default:[]))
                    then unsupported at "A history contract in a checked module binding"
                    else Ok ()
                  in
                  let target =
                    if not (is_pure f) then proc_name f
                    else
                      match List.Assoc.find !publications f.id ~equal:Ident.same with
                      | Some publication -> publication
                      | None ->
                          let publication = fresh ("published_" ^ f.raven_name) in
                          let body =
                            forwarding_body actual_ctx ~at ~self:publication
                              ~target:(proc_name f) ~result:f.body.exp_type ~atomic:false
                              prepared
                          in
                          publications := (f.id, publication) :: !publications;
                          publication_members :=
                            ( binding,
                              prepared_member ~at ~name:publication (Some body) prepared
                            )
                            :: !publication_members;
                          publication
                  in
                  let projection =
                    List.fold all_resource_views ~init:Subst.identity
                      ~f:(fun projection resource ->
                        let path =
                          Path.Pdot (binding.actual_path, resource.Source.resource_name)
                        in
                        if
                          Path.same
                            (Proof_bindings.canonical_owner scoped_proofs
                               resource.resource_path)
                            (Proof_bindings.canonical_owner scoped_proofs path)
                        then Subst.add_module resource.resource_id path projection
                        else projection)
                  in
                  let projection =
                    List.fold types ~init:projection ~f:(fun projection data ->
                        match data.Datatypes.id with
                        | None -> projection
                        | Some id -> (
                            match
                              List.find data.paths ~f:(function
                                | Path.Pdot (parent, _) ->
                                    Path.same parent binding.actual_path
                                | _ -> false)
                            with
                            | None -> projection
                            | Some path -> Subst.add_type id path projection))
                  in
                  Ok (prepared, f.contract, projection, f.loc, target)
              | None ->
                  let library =
                    List.find libraries ~f:(fun lib ->
                        Path.same lib.Library_modules.library_path binding.actual_path)
                  in
                  begin match library with
                  | None ->
                      unsupported at
                        "A checked module argument without a supported operation contract"
                  | Some lib ->
                      let* contracts = interface_contracts lib.library in
                      let contract =
                        Option.map
                          (List.Assoc.find contracts member ~equal:String.equal)
                          ~f:fst
                      in
                      let* () = check_adapter_shape ~at contract in
                      let value = Env.find_value actual_path binding.site.environment in
                      let actual_args, actual_result =
                        Signature_contract.arguments value.val_type
                      in
                      let own_preds =
                        List.filter_map library_preds ~f:(fun (library, p, ts) ->
                            Option.some_if
                              (Path.same library.Library_modules.library_path
                                 lib.library_path)
                              ( p.S.pred_name.pid_str,
                                (library.library_name ^ "." ^ p.pred_name.pid_str, ts) ))
                      in
                      let own_inputs =
                        List.filter_map own_preds ~f:(fun (local, (target, _)) ->
                            Option.map
                              (List.Assoc.find proof_support.predicate_inputs target
                                 ~equal:String.equal) ~f:(fun count -> (local, count)))
                      in
                      let* environment = Library_modules.environment source lib in
                      let actual_ctx =
                        scoped_contract_context types ~refs ~primitives ~shared
                          ~environment ~proof_support ~preds ~spec_funcs ~own_preds
                          ~own_inputs origins
                      in
                      let* prepared =
                        prepare_callable actual_ctx ~at:value.val_loc ~args:actual_args
                          ~result:actual_result contract
                      in
                      Ok
                        ( prepared,
                          contract,
                          Subst.identity,
                          value.val_loc,
                          lib.library_name ^ "." ^ member )
                  end)
        in
        let* () =
          if
            Bool.equal
              (logical_contract actual_contract)
              (logical_contract operation.operation_contract)
          then Ok ()
          else
            error at
              "The module operation has a different ordinary or logically atomic \
               contract kind"
        in
        let expected_implicit = expected.prepared_implicit
        and actual_implicit = actual.prepared_implicit in
        let* () =
          if
            List.length expected_implicit = List.length actual_implicit
            && Poly.equal expected.prepared_roles actual.prepared_roles
          then Ok ()
          else
            unsupported at
              "Different implicit argument shapes in a checked module binding"
        in
        let* () =
          if
            List.for_all2_exn expected_implicit actual_implicit
              ~f:(fun (_, _, a, _, _) (_, _, b, _, _) ->
                Ctype.is_equal
                  (Source.annotation_env source binding.site.environment)
                  false
                  [ Subst.type_expr view.view_actual_substitution a ]
                  [
                    Subst.type_expr binding.parameter_substitution
                      (Subst.type_expr actual_projection b);
                  ])
          then Ok ()
          else error at "The module operation has different implicit argument types"
        in
        let* () =
          if
            List.exists
              (args @ [ result ]
              @ List.map expected_implicit ~f:(fun (_, _, t, _, _) -> t))
              ~f:(contains_atomic_token view.view_types)
          then unsupported at "Public atomic-update tokens in a checked module binding"
          else Ok ()
        in
        let body =
          forwarding_body ctx ~at ~self:operation.operation_name ~target:actual_name
            ~result
            ~atomic:(logical_contract operation.operation_contract)
            expected
        in
        let related =
          [
            (signature.site.item_loc, "The requested module operation");
            (actual_at, "The actual module operation");
          ]
        in
        List.iter
          [
            ( R.Diagnostic.Precondition,
              "The module argument's precondition is not provided by this view" );
            ( Postcondition,
              "The module argument does not establish this view's postcondition" );
            ( Commit,
              "The module argument does not establish this view's atomic postcondition" );
            ( Abortable_call,
              "This view's atomic update may not be restorable if the actual operation \
               aborts" );
          ]
          ~f:(fun (code, message) ->
            origins := { at; code; message; related } :: !origins);
        origins :=
          {
            at = { at with loc_start = at.loc_end };
            code = Postcondition;
            message = "The module argument does not establish this view's postcondition";
            related;
          }
          :: !origins;
        List.iter operation.operation_paths ~f:(fun path ->
            let projection =
              match path with
              | Path.Pdot (parent, _) -> checked_type_substitution binding parent
              | _ -> view.view_source_substitution
            in
            checked_prepared :=
              ( path,
                ( expected,
                  operation.operation_contract,
                  projection,
                  signature.site.item_loc,
                  operation.operation_name ) )
              :: !checked_prepared);
        Ok
          ( operation,
            expected,
            prepared_member ~at ~name:operation.operation_member (Some body) expected ))
  in
  let symbolic_view group owner =
    let view =
      List.find_exn checked_views ~f:(fun view ->
          phys_equal view.view_binding group.Generic_modules.representative.argument)
    in
    {
      view with
      view_types =
        Generic_modules.types group ~owner
        @ (let root =
             List.find_exn generics ~f:(fun root ->
                 String.equal root.Generic_modules.name group.name)
           in
           Option.value_map root.world ~default:[] ~f:(fun world ->
               List.concat_map (Generic_modules.parameter_groups root) ~f:(fun stage ->
                   Generic_modules.world_types stage ~owner:[ world ])))
        @ types;
      view_resources =
        List.map view.view_resources ~f:(fun (formal, resource) ->
            let stem =
              List.Assoc.find_exn group.resources
                formal.Module_inventory.declaration.pred_name.pid_str ~equal:String.equal
            in
            ( formal,
              {
                resource with
                resource_backend = String.concat ~sep:"." (owner @ [ stem ]);
              } ));
    }
  in
  let resource_members group view ~aliases =
    all view.view_resources ~f:(fun (formal, resource) ->
        let p = formal.Module_inventory.declaration in
        let l = loc p.pred_name.pid_loc in
        let environment = Source.annotation_env source formal.site.environment in
        let* parameter_types =
          all p.pred_params ~f:(fun (id, pty) ->
              Source.ocaml_type environment ~at:id.S.pid_loc pty)
        in
        let* vars =
          all (List.zip_exn p.pred_params parameter_types) ~f:(fun ((id, _), t) ->
              let* typ = Datatypes.typ view.view_types ~at:id.S.pid_loc t in
              Ok (R.Var.make ~loc:l (ident ~loc:l id.pid_str) typ))
        in
        let* outputs = predicate_output_count view.view_types p parameter_types in
        let formals, returns = List.split_n vars (List.length vars - outputs) in
        let stem =
          List.Assoc.find_exn group.Generic_modules.resources p.pred_name.pid_str
            ~equal:String.equal
        in
        let member =
          if aliases then
            let kind =
              if p.pred_persistent then R.Callable.Invariant else R.Callable.Predicate
            in
            R.Callable.resource_alias ~loc:l ~kind ~formals ~returns (ident ~loc:l stem)
              (qualified_name ~loc:l resource.resource_backend)
          else
            let kind = if p.pred_persistent then R.Callable.Inv else R.Callable.Pred in
            R.Callable.func ~loc:l ~kind ~formals ~returns (ident ~loc:l stem) None
        in
        Ok (R.Member.callable member))
  in
  let type_members group view ~aliases =
    let* members =
      all view.view_binding.expected.signature_types ~f:(fun (source, declaration) ->
          if
            aliases
            && (Option.is_some group.Generic_modules.world
               || Option.is_some declaration.Typedtree.typ_manifest)
          then Ok None
          else
            let at = declaration.Typedtree.typ_loc in
            let l = loc at in
            let* definition =
              if aliases then
                let t =
                  Btype.newgenty
                    (Tconstr (Path.Pident declaration.typ_id, [], ref Types.Mnil))
                in
                Result.map (Datatypes.typ view.view_types ~at t) ~f:Option.some
              else
                match (group.Generic_modules.world, declaration.typ_manifest) with
                | Some world, _ ->
                    let stem =
                      List.Assoc.find_exn group.types source ~equal:String.equal
                    in
                    Ok
                      (Some
                         (R.Type.named ~loc:l
                            (R.Name.make ~loc:l ~path:[ world ] stem)
                            []))
                | None, None -> Ok None
                | None, Some t ->
                    Result.map
                      (Datatypes.typ view.view_types ~at t.ctyp_type)
                      ~f:Option.some
            in
            let stem =
              List.Assoc.find_exn group.Generic_modules.types source ~equal:String.equal
            in
            Ok (Some (R.Member.type_ ~loc:l (ident ~loc:l stem) definition)))
    in
    Ok (List.filter_opt members)
  in
  let ghost_contract_members ?(carrier_interface = fun _ -> None) ~aliases ~implementation
      ~scope ~path ~at signature =
    all signature.Module_inventory.signature_ghost_modules ~f:(fun (member, formal) ->
        let declaration = formal.Module_inventory.ghost_declaration in
        let at = declaration.S.ghost_module_name.pid_loc in
        let l = loc at in
        let* signatures = Proof_library.signatures at in
        let* interface =
          match
            Proof_library.find signatures
              (Proof_library.path_of_qualid declaration.ghost_module_interface)
          with
          | Some interface
            when interface.interface
                 && Proof_library.is_resource_algebra signatures interface ->
              Ok interface
          | Some _ | None ->
              error at "An abstract proof module must name a resource algebra interface"
        in
        let interface_name =
          Option.value (carrier_interface member)
            ~default:(qualified_name ~loc:l (String.concat ~sep:"." interface.path))
        in
        if not aliases then
          Ok (R.Member.instance ~loc:l (ident ~loc:l member) interface_name)
        else
          let wanted =
            Proof_bindings.canonical_owner scoped_proofs (Path.Pdot (path, member))
          in
          match
            List.find all_resources ~f:(fun resource ->
                Source.resource_has_path resource wanted
                || Path.same wanted
                     (Proof_bindings.canonical_owner scoped_proofs
                        resource.Source.resource_path))
          with
          | None -> error at ("The actual module does not declare proof module " ^ member)
          | Some resource ->
              let resource =
                if implementation then resource else resource_view ~scope resource
              in
              if
                not
                  (List.exists resource.resource_interfaces
                     ~f:(List.equal String.equal interface.path))
              then
                error at
                  ("The proof module " ^ member ^ " does not implement "
                  ^ String.concat ~sep:"." interface.path)
              else
                Ok
                  (match carrier_interface member with
                  | None ->
                      R.Member.alias ~loc:l (ident ~loc:l member)
                        (qualified_name ~loc:l resource.resource_backend)
                  | Some typ ->
                      R.Member.checked_view ~loc:l ~typ (ident ~loc:l member)
                        (qualified_name ~loc:l resource.resource_backend)))
  in
  let ghost_module_members ~aliases (binding : Module_inventory.checked_binding) =
    let carrier_interface member =
      Option.bind (Generic_modules.application_for_binding generics binding)
        ~f:(fun (stage, application) ->
          Option.map stage.world ~f:(fun world ->
              let owner = if aliases then application.world else world in
              qualified_name ~loc:(loc binding.site.item_loc)
                (owner ^ "." ^ Generic_modules.algebra_name stage member)))
    in
    ghost_contract_members ~carrier_interface ~aliases ~implementation:false
      ~scope:(Proof_bindings.scope_for_location scoped_proofs binding.site.item_loc)
      ~path:binding.actual_path ~at:binding.site.item_loc binding.expected
  in
  let* _ =
    all inventory.constraints ~f:(fun constraint_ ->
        match
          Option.first_some constraint_.Module_inventory.result_owner constraint_.owner
        with
        | None -> Ok []
        | Some path ->
            ghost_contract_members ~aliases:true ~implementation:true ~scope:None ~path
              ~at:constraint_.at constraint_.signature)
  in
  let* _ =
    all inventory.bindings ~f:(fun binding -> ghost_module_members ~aliases:true binding)
  in
  let* generic_interfaces =
    all generics ~f:(fun owner ->
        all (Generic_modules.parameter_groups owner) ~f:(fun group ->
            let view = symbolic_view group (String.split group.interface ~on:'.') in
            let* types = type_members group view ~aliases:false in
            let* resources = resource_members group view ~aliases:false in
            let* ghost_modules =
              ghost_module_members ~aliases:false group.representative.argument
            in
            let* operations =
              all checked_operations ~f:(fun operation ->
                  if
                    not
                      (phys_equal operation.operation_binding
                         group.representative.argument)
                  then Ok None
                  else
                    let* _, _, _, prepared = prepare_view_operation view operation in
                    Ok
                      (Some
                         (R.Member.callable
                            (prepared_member
                               ~at:operation.operation_signature.site.item_loc
                               ~name:operation.operation_member None prepared))))
            in
            let l = loc group.representative.argument.site.item_loc in
            let carriers =
              Option.value_map group.world ~default:[] ~f:(fun world ->
                  List.map group.representative.argument.expected.signature_ghost_modules
                    ~f:(fun (member, _) ->
                      R.Member.module_ ~loc:l ~interface:true
                        ~implements:
                          [ (qualified_name ~loc:l "Library.ResourceAlgebra", []) ]
                        (ident ~loc:l (Generic_modules.algebra_name group member))
                        [
                          R.Member.type_ ~loc:l ~rep:true (ident ~loc:l "T")
                            (Some
                               (R.Type.named ~loc:l
                                  (qualified_name ~loc:l
                                     (world ^ "."
                                     ^ Generic_modules.carrier_name group member))
                                  []));
                        ]))
            in
            Ok
              (carriers
              @ [
                  R.Member.module_ ~loc:l ~interface:true
                    (ident ~loc:l (Qualified_name.of_string group.interface).name)
                    (types @ resources @ ghost_modules @ List.filter_opt operations);
                ])))
    |> Result.map ~f:(List.map ~f:List.concat)
  in
  let* checked_module_members =
    all checked_modules ~f:(fun view ->
        let at = view.Checked_modules.binding.site.item_loc in
        let l = loc at in
        let members =
          List.filter adapter_members ~f:(fun (operation, _, _) ->
              phys_equal operation.operation_binding view.binding)
        in
        match (view.grouped, view.target) with
        | false, _ ->
            Ok (List.map members ~f:(fun (_, _, member) -> R.Member.callable member))
        | true, Some target ->
            Ok
              [
                R.Member.checked_view ~loc:l
                  ~typ:(qualified_name ~loc:l view.interface)
                  (ident ~loc:l view.name) (name ~loc:l target);
              ]
        | true, None ->
            let declarations =
              List.map members ~f:(fun (operation, prepared, _) ->
                  R.Member.callable
                    (prepared_member ~at:operation.operation_signature.site.item_loc
                       ~name:operation.operation_member None prepared))
            in
            let* prefix, aliases =
              match Generic_modules.application_for_binding generics view.binding with
              | None ->
                  Ok
                    ( [
                        R.Member.module_ ~loc:l ~interface:true
                          (ident ~loc:l view.interface) declarations;
                      ],
                      [] )
              | Some (group, _) ->
                  let concrete =
                    List.find_exn checked_views ~f:(fun checked ->
                        phys_equal checked.view_binding view.binding)
                  in
                  let* types = type_members group concrete ~aliases:true in
                  let* resources = resource_members group concrete ~aliases:true in
                  let* ghost_modules = ghost_module_members ~aliases:true view.binding in
                  Ok ([], types @ resources @ ghost_modules)
            in
            Ok
              (prefix
              @ [
                  R.Member.module_ ~loc:l
                    ~implements:[ (qualified_name ~loc:l view.interface, []) ]
                    (ident ~loc:l view.name)
                    (aliases
                    @ List.map members ~f:(fun (_, _, member) -> R.Member.callable member)
                    );
                ]))
  in
  (* The checks that the actions keep the histories' orders. *)
  let* action_check_lists =
    all structures ~f:(fun st ->
        let preds, spec_funcs, proof_support =
          proof_context_for ~preds ~spec_funcs ~proof_support st.invariant
        in
        let* members =
          action_checks
            (spec_context types ~refs ~primitives
               ~shared:(shared_for_proof st.invariant)
               ~ocaml_env:st.environment ~preds ~spec_funcs ~proof_support origins)
            st
        in
        Ok (st, members))
  in
  let* pending_member_lists =
    all structures ~f:(fun st ->
        let* members =
          all st.pendings ~f:(fun p ->
              match List.find funcs ~f:(fun f -> Ident.same f.id p.helped) with
              | Some helped ->
                  let preds, spec_funcs, proof_support =
                    proof_context_for ~preds ~spec_funcs ~proof_support st.invariant
                  in
                  pending_members
                    (spec_context types ~refs ~primitives
                       ~shared:(shared_for_proof st.invariant)
                       ~ocaml_env:st.environment ~preds ~spec_funcs ~proof_support origins)
                    st p helped
                    ~helped_proc:
                      (match owner_destination st.invariant with
                      | Module_context.Flat -> proc_name helped
                      | Module_context.Worker _ -> body_proc_name helped)
              | None ->
                  error st.at
                    (Printf.sprintf "There is no function %s to help"
                       (Ident.name p.helped)))
        in
        Ok (st, List.concat members))
  in
  let* pred_members =
    all predicates ~f:(fun (at, p, def, param_types) ->
        let preds, spec_funcs, proof_support =
          proof_context_for ~preds ~spec_funcs ~proof_support p.pred_name.pid_str
        in
        predicate types ~refs ~primitives
          ~shared:(shared_for_proof p.pred_name.pid_str)
          ~ocaml_env:(declaration_environment p.pred_name.pid_str)
          ~preds ~spec_funcs ~proof_support
          ?declaration_name:(definition_member_name p.pred_name.pid_str)
          origins ~at ~structures p def param_types)
  in
  let predicate_bodies =
    List.filter_map predicates ~f:(fun (_, p, definition, _) ->
        match definition with
        | (Body body | Direct_invariant body)
          when Option.is_none (scoped_binding p.pred_name.pid_str) ->
            Some
              ( p.S.pred_name.pid_str,
                { definition = body; environment = ocaml_env; project_type = Fn.id } )
        | Body _ | Direct_invariant _ -> None
        | Invariant _ | View _ -> None)
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        match binding.kind with
        | Predicate (_, Plain body)
          when binding.exported && not (Proof_bindings.opaque scoped_proofs binding) ->
            Some
              ( binding.public_key,
                {
                  definition = body;
                  environment = binding.environment;
                  project_type = Proof_bindings.public_type scoped_proofs;
                } )
        | _ -> None)
  in
  let body_contexts ?at scope =
    let owners = context_owners at in
    let environment =
      Option.value_map scope ~default:source.env ~f:(fun scope ->
          Source.annotation_env source scope.Proof_scopes.environment)
    in
    let project = Proof_bindings.context_type scoped_proofs ~environment in
    let predicate_bodies =
      List.filter_map scoped_proofs.bindings ~f:(fun binding ->
          match binding.kind with
          | Predicate (_, Plain body)
            when Proof_bindings.visible scoped_proofs ~scope binding
                 && not (Proof_bindings.opaque_at scoped_proofs ~scope binding) ->
              Some
                ( binding.public_key,
                  {
                    definition = body;
                    environment = binding.environment;
                    project_type = Proof_bindings.public_type scoped_proofs;
                  } )
          | _ -> None)
      @ predicate_bodies
    in
    let predicate_bodies =
      List.map predicate_bodies ~f:(fun (key, body) ->
          (key, { body with project_type = (fun ty -> project (body.project_type ty)) }))
    in
    let predicate_bodies =
      List.filter_map scoped_proofs.applications ~f:(fun view ->
          match view.source.kind with
          | Predicate (_, Plain body)
            when Proof_bindings.application_visible ~owners scoped_proofs ~scope view
                 && not
                      (Proof_bindings.application_opaque ~owners scoped_proofs ~scope view)
            ->
              Some
                ( view.key,
                  {
                    definition = body;
                    environment = view.source.environment;
                    project_type = (fun ty -> project (view.project_type ty));
                  } )
          | _ -> None)
      @ predicate_bodies
    in
    List.filter_map (Proof_bindings.private_bindings scoped_proofs ~scope)
      ~f:(fun binding ->
        match binding.kind with
        | Predicate (_, Plain body) ->
            Some
              ( binding.backend,
                {
                  definition = body;
                  environment = binding.environment;
                  project_type = Fn.id;
                } )
        | _ -> None)
    @ predicate_bodies
  in
  let module_lemmas context ~project lemmas =
    List.map lemmas ~f:(fun (key, signature) ->
        let backend =
          match scoped_binding signature.lemma_raven with
          | Some binding when Module_context.contains context binding ->
              Module_context.member context binding.backend
          | _ -> signature.lemma_raven
        in
        ( key,
          {
            signature with
            lemma_raven = backend;
            lemma_inputs = List.map signature.lemma_inputs ~f:project;
            lemma_outputs = List.map signature.lemma_outputs ~f:project;
          } ))
  in
  let* lemma_members =
    all lemma_declarations ~f:(fun declaration ->
        let declaration_name = (Proof_scopes.name declaration).pid_str in
        let scope = declaration_scope declaration_name in
        let preds, spec_funcs, proof_support =
          proof_context_for ~preds ~spec_funcs ~proof_support declaration_name
        in
        let lemmas = lemma_context scope in
        let lemmas =
          module_lemmas (declaration_context declaration_name) ~project:Fn.id lemmas
        in
        proof_lemma types ~refs ~primitives ~shared
          ~ocaml_env:(declaration_environment declaration_name)
          ~preds ~spec_funcs ~proof_lemmas:lemmas ~proof_support
          ~predicate_bodies:(body_contexts scope)
          ?member_name:(definition_member_name declaration_name)
          origins declaration)
  in
  let* logical_members =
    all
      (List.mapi logical_declarations ~f:(fun i declaration -> (i, declaration)))
      ~f:(fun (i, declaration) ->
        let declaration_name = (Proof_scopes.name declaration).pid_str in
        let scope = declaration_scope declaration_name in
        let preds, spec_funcs, proof_support =
          proof_context_for ~preds ~spec_funcs ~proof_support declaration_name
        in
        let previous =
          List.map (List.take logical_declarations i) ~f:(fun declaration ->
              (Proof_scopes.name declaration).pid_str)
        in
        let implementation_key backend =
          Option.value
            (List.find_map scoped_proofs.bindings ~f:(fun binding ->
                 Option.some_if
                   (Option.equal String.equal (definition_target binding) (Some backend))
                   binding.backend))
            ~default:
              (Option.value
                 (List.find_map scoped_proofs.applications ~f:(fun view ->
                      Option.some_if
                        (String.equal view.backend backend)
                        view.source.backend))
                 ~default:
                   (Option.value
                      (List.find_map scoped_proofs.bindings ~f:(fun binding ->
                           Option.bind (proof_worker binding.backend) ~f:(fun plan ->
                               Option.some_if
                                 (String.equal
                                    (Generic_proofs.member plan binding.backend)
                                    backend)
                                 binding.backend)))
                      ~default:backend))
        in
        let available signature =
          List.mem previous (implementation_key signature.lemma_raven) ~equal:String.equal
        in
        let logical_functions =
          List.filter proof_support.logical_functions ~f:(fun (_, signature) ->
              available signature)
        in
        let spec_funcs =
          List.filter spec_funcs ~f:(fun (key, _) ->
              match
                List.Assoc.find proof_support.logical_functions key ~equal:String.equal
              with
              | None -> true
              | Some signature -> available signature)
        in
        let* () =
          match declaration with
          | S.Proof_function { function_params; function_body; _ } ->
              let environment = declaration_environment declaration_name in
              let bound = List.map function_params ~f:(fun (id, _) -> id.S.pid_str) in
              Result.all_unit
                (List.map (term_references bound function_body) ~f:(fun q ->
                     let key =
                       Option.value
                         (Proof_bindings.resolve scoped_proofs ~scope ~environment q)
                         ~default:(qualid_key q)
                     in
                     let key =
                       Option.value
                         (Proof_bindings.canonical_key scoped_proofs key)
                         ~default:key
                     in
                     if
                       List.Assoc.mem all_logical_functions key ~equal:String.equal
                       && not (List.mem previous key ~equal:String.equal)
                     then
                       error (S.qualid_loc q)
                         "A logical function can only call earlier logical definitions"
                     else Ok ()))
          | _ -> Ok ()
        in
        proof_function types ~refs ~primitives ~shared
          ~ocaml_env:(declaration_environment declaration_name)
          ~preds ~spec_funcs
          ~proof_support:{ proof_support with logical_functions }
          ?member_name:(definition_member_name declaration_name)
          ~as_value:
            (match declaration with
            | S.Proof_function { function_params = []; _ } -> true
            | _ -> false)
          origins declaration)
  in
  let pure_functions =
    Path_bindings.of_list
      (List.concat_map pure ~f:(fun f ->
           List.map f.paths ~f:(fun path -> (path, pure_name f))))
  in
  let* runtime_contexts =
    all runtime_destinations ~f:(fun destination ->
        let groups = Module_context.groups destination in
        let namespace = Module_context.namespace destination in
        let* layouts =
          all groups ~f:(fun group ->
              Result_layouts.symbolic layouts group ~owner:(namespace @ [ "Layout" ]))
        in
        let body_types =
          List.concat layouts
          @ List.concat_map groups ~f:(fun group ->
              Generic_modules.worker_types group ~owner:namespace)
          @ types
        in
        let stages = List.concat_map groups ~f:Generic_modules.parameter_groups in
        let predicate_overrides =
          List.filter_map checked_resource_entries ~f:(fun (path, key, _, ts) ->
              match path with
              | Path.Pdot (parent, member) ->
                  List.find_map stages ~f:(fun stage ->
                      if
                        List.mem stage.representative.argument.paths parent
                          ~equal:Path.same
                      then
                        Option.map
                          (List.Assoc.find stage.resources member ~equal:String.equal)
                          ~f:(fun stem ->
                            ( key,
                              ( String.concat ~sep:"."
                                  (namespace @ [ stage.parameter; stem ]),
                                ts ) ))
                      else None)
              | _ -> None)
        in
        let representatives =
          List.filter funcs ~f:(fun f ->
              List.exists groups ~f:(fun group ->
                  List.exists group.representative.members ~f:(fun (_, id) ->
                      Ident.same id f.id)))
        in
        let map_functions ?(only_pure = false) initial target =
          let selected =
            if only_pure then List.filter representatives ~f:is_pure else representatives
          in
          List.fold selected ~init:initial ~f:(fun mappings f ->
              List.fold f.paths ~init:mappings ~f:(fun mappings path ->
                  Path_bindings.add mappings path (target f)))
        in
        let body_functions = map_functions functions body_proc_name in
        let body_functions =
          List.fold checked_operations ~init:body_functions ~f:(fun mappings operation ->
              match
                List.find stages ~f:(fun stage ->
                    phys_equal operation.operation_binding stage.representative.argument)
              with
              | None -> mappings
              | Some stage ->
                  List.fold operation.operation_paths ~init:mappings
                    ~f:(fun mappings path ->
                      Path_bindings.add mappings path
                        (String.concat ~sep:"."
                           (namespace @ [ stage.parameter; operation.operation_member ]))))
        in
        Ok
          ( destination,
            {
              body_types;
              predicate_overrides;
              calls = body_functions;
              pure_calls = map_functions ~only_pure:true pure_functions body_pure_name;
              representatives;
              logical_calls =
                map_functions ~only_pure:true proof_support.runtime_functions
                  body_pure_reference;
            } ))
  in
  let body_context f =
    let context = body_module_context f in
    let preds, spec_funcs, proof_support =
      module_context context ~projection:context.projection
        (proof_context ~current_procedure:(proc_name f) ~at:f.loc (Some context.scope)
           preds spec_funcs proof_support)
    in
    let plan =
      List.Assoc.find_exn runtime_contexts (body_destination f)
        ~equal:Module_context.same_destination
    in
    let body_spec_funcs =
      List.map spec_funcs ~f:(fun (source, target) ->
          let target =
            match List.Assoc.find plan.predicate_overrides source ~equal:String.equal with
            | Some (target, _) -> target
            | None ->
                Option.value_map
                  (List.find plan.representatives ~f:(fun f ->
                       String.equal target (pure_name f)))
                  ~default:target ~f:body_pure_name
          in
          (source, target))
    in
    let body_proof_support =
      { proof_support with runtime_functions = plan.logical_calls }
    in
    ( plan.body_types,
      plan.predicate_overrides @ preds,
      plan.calls,
      plan.pure_calls,
      body_spec_funcs,
      body_proof_support )
  in
  let runtime_primitives =
    List.map runtime_destinations ~f:(fun destination ->
        ( destination,
          if Module_context.same_destination destination Module_context.Flat then
            primitives
          else ref [] ))
  in
  let body_primitives f =
    let destination = body_destination f in
    ( List.Assoc.find_exn runtime_primitives destination
        ~equal:Module_context.same_destination,
      Module_context.namespace destination )
  in
  let body_environment f =
    let context = body_module_context f in
    let* environment =
      List.fold_result (Module_context.parameter_pairs context) ~init:f.environment
        ~f:(fun environment (original, target) ->
          Source.project_ghost_parameter source ~original ~target environment)
    in
    let environment =
      List.fold (Module_context.runtime_pairs context) ~init:environment
        ~f:(fun environment (original, target) ->
          let declaration =
            {
              original.Typedtree.typ_type with
              type_kind = Types.Type_abstract Types.Definition;
              type_manifest = Some (Ctype.newconstr (Path.Pident target.typ_id) []);
              type_private = Asttypes.Public;
            }
          in
          Env.add_type ~check:false original.typ_id declaration environment)
    in
    if List.is_empty context.parameters then Ok environment
    else Ok (Source.annotation_env ~at:f.loc source environment)
  in
  let* pure_funcs =
    all pure ~f:(fun f ->
        match body_owner f with
        | Some (_, false) -> Ok None
        | _ ->
            let* environment = body_environment f in
            let f = { f with environment } in
            let data, predicates, _, pure_functions, spec_funcs, proof_support =
              body_context f
            in
            let declaration_name =
              Module_context.local_name (body_destination f) (body_pure_name f)
            in
            let primitives, primitive_namespace = body_primitives f in
            let* member =
              func data ~refs ~primitives ~shared:(body_shared f) ~ocaml_env:f.environment
                ~preds:predicates ~funcs:pure_functions ~spec_funcs ~proof_support
                ~declaration_name ~primitive_namespace origins f
            in
            Ok (Some (f, member)))
  in
  let* procs =
    all funcs ~f:(fun f ->
        match body_owner f with
        | Some (_, false) -> Ok None
        | _ ->
            let* environment = body_environment f in
            let f = { f with environment } in
            let data, predicates, functions, _, spec_funcs, proof_support =
              body_context f
            in
            let declaration_name =
              Module_context.local_name (body_destination f) (body_proc_name f)
            in
            let primitives, primitive_namespace = body_primitives f in
            let* member =
              proc data ~refs ~primitives ~shared:(body_shared f) ~ocaml_env:f.environment
                ~preds:predicates ~funcs:spec_funcs ~annotations ~access_proofs
                ~return_proofs ~initializations ~linearizations ~lifted ~pasts
                ~past_structures:(past_structures ~symbolic:true f)
                ~past_returns ~ghost_args ~procedure_signatures
                ~proof_lemmas:
                  (let context = body_module_context f in
                   module_lemmas context
                     ~project:(Module_context.project_type context)
                     (lemma_context ~at:f.loc (Some context.scope)))
                ~proof_support
                ~predicate_bodies:
                  (let context = body_module_context f in
                   List.map (body_contexts ~at:f.loc (Some context.scope))
                     ~f:(fun (key, body) ->
                       ( key,
                         {
                           body with
                           project_type =
                             (fun typ ->
                               Module_context.project_type context (body.project_type typ));
                         } )))
                ~libraries:(library_paths libraries) functions origins
                ~proc_name:(body_proc_name f) ~pure:(is_pure f) ~declaration_name
                ~primitive_namespace ~pure_name:(body_pure_reference f) f
            in
            Ok (Some (f, member)))
  in
  let pure_funcs = List.filter_opt pure_funcs and procs = List.filter_opt procs in
  let owned destination members =
    List.filter members ~f:(fun (f, _) ->
        Module_context.same_destination destination (body_destination f))
  in
  let procedure_member (f, member) =
    if f.trusted then R.Member.free (R.Member.callable member)
    else R.Member.callable member
  in
  let predicate_members =
    List.zip_exn
      (List.map predicates ~f:(fun (_, p, _, _) -> p.S.pred_name.pid_str))
      pred_members
  in
  let proof_lemma_members =
    List.zip_exn
      (List.map lemma_declarations ~f:(fun d -> (Proof_scopes.name d).pid_str))
      lemma_members
  in
  let logical_members =
    List.zip_exn
      (List.map logical_declarations ~f:(fun d -> (Proof_scopes.name d).pid_str))
      logical_members
  in
  let proof_members =
    List.map (predicate_members @ proof_lemma_members) ~f:(fun (name, member) ->
        (name, R.Member.callable member))
    @ logical_members
  in
  let* definition_modules =
    all
      (List.filter source.proof_resources ~f:(fun resource ->
           resource.Source.resource_definition
           && Option.is_none resource.resource_application))
      ~f:(fun resource ->
        let at = resource.resource_at in
        let l = loc at in
        let* backend, representation =
          match (implementation resource, resource.resource_representation) with
          | Some backend, Some representation -> Ok (backend, representation)
          | _ -> error at "Missing resource algebra representation"
        in
        let* representation = Datatypes.typ types ~at representation in
        let carrier =
          R.Member.type_ ~loc:l ~rep:true (ident ~loc:l "T") (Some representation)
        in
        let members =
          List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
              Option.bind
                (List.find scoped_proofs.bindings ~f:(fun binding ->
                     Ident.same binding.entry.id entry.id
                     && (match binding.kind with Function _ -> true | _ -> false)
                     && Option.exists (definition_resource binding.entry.scope)
                          ~f:(fun owner ->
                            Ident.same owner.resource_id resource.resource_id)))
                ~f:(fun binding ->
                  List.Assoc.find proof_members binding.backend ~equal:String.equal))
        in
        let interface =
          qualified_name ~loc:l (String.concat ~sep:"." resource.resource_functor)
        in
        Ok
          ( resource,
            R.Member.module_ ~loc:l
              ~implements:[ (interface, []) ]
              (ident ~loc:l backend) (carrier :: members) ))
  in
  let definition_proof_modules =
    List.filter_map source.proof_resources ~f:(fun resource ->
        if
          (not resource.resource_definition)
          || Option.is_some resource.resource_application
        then None
        else
          Option.bind (proof_implementation resource) ~f:(fun backend ->
              let members =
                List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
                    Option.bind
                      (List.find scoped_proofs.bindings ~f:(fun binding ->
                           Ident.same binding.entry.id entry.id
                           && (match binding.kind with
                             | Predicate _ | Lemma _ -> true
                             | _ -> false)
                           && Option.exists (definition_resource binding.entry.scope)
                                ~f:(fun owner ->
                                  Ident.same owner.resource_id resource.resource_id)))
                      ~f:(fun binding ->
                        List.Assoc.find proof_members binding.backend ~equal:String.equal))
              in
              Option.some_if
                (not (List.is_empty members))
                ( resource,
                  R.Member.module_ ~loc:(loc resource.resource_at)
                    (ident ~loc:(loc resource.resource_at) backend)
                    members )))
  in
  let emitted_proofs destination members =
    List.filter_map members ~f:(fun (name, member) ->
        Option.some_if
          (Module_context.same_destination (owner_destination name) destination
          && Option.is_none (Option.bind (scoped_binding name) ~f:definition_target))
          member)
  in
  let emitted_assets destination members =
    List.filter_map members ~f:(fun (resource, member) ->
        Option.some_if
          (Module_context.emits_owner module_contexts ~destination
             resource.Source.resource_scope)
          member)
  in
  let emitted_fields destination fields =
    List.filter_map fields ~f:(fun (field, member) ->
        Option.some_if
          (Module_context.emits_owner module_contexts ~destination
             field.Source.field_scope)
          member)
  in
  let* explicit_fields =
    all source.proof_fields ~f:(fun field ->
        let l = loc field.Source.field_at in
        let* value_type =
          match field.field_resource with
          | None ->
              begin match
                List.find all_resource_views ~f:(fun resource ->
                    resource.resource_is_ra
                    && same_named_type field.field_value resource.resource_type)
              with
              | None -> Datatypes.typ types ~at:field.field_at field.field_value
              | Some resource ->
                  Ok
                    (R.Type.named ~loc:l
                       (qualified_name ~loc:l resource.resource_backend)
                       [])
              end
          | Some owner ->
              begin match
                List.find all_resource_views ~f:(fun resource ->
                    Source.resource_has_path resource owner)
              with
              | None -> error field.field_at "Unknown resource algebra for field"
              | Some resource ->
                  let private_representation =
                    resource.resource_definition
                    && Option.exists resource.resource_representation ~f:(fun rep ->
                        same_named_type field.field_value rep)
                  in
                  let* backend =
                    if private_representation then
                      match implementation resource with
                      | Some backend -> Ok backend
                      | None ->
                          error field.field_at "Missing resource algebra implementation"
                    else Ok resource.resource_backend
                  in
                  if resource.resource_is_ra then
                    Ok (R.Type.named ~loc:l (qualified_name ~loc:l backend) [])
                  else error field.field_at "The field resource is not a resource algebra"
              end
        in
        Ok
          ( field,
            Datatypes.field_member ~ghost:true types ~loc:l
              (Qualified_name.of_string (ghost_field_name field)).name value_type
              field.field_value ))
  in
  let emit_context_members destination ~at ~representations ~native_resources
      ~applications ~late_members =
    let group = List.hd (Module_context.groups destination) in
    let ghost_fields =
      List.filter_map view_fields ~f:(fun (_, (field, typ, init)) ->
          Option.some_if
            (Option.is_none init && same_group (field_group field) group)
            (R.Member.field ~loc:at ~ghost:true
               (ident ~loc:at (Module_context.local_name destination field))
               typ))
    in
    let primitive_members =
      !(List.Assoc.find_exn runtime_primitives destination
          ~equal:Module_context.same_destination)
      |> List.map ~f:snd
    in
    let stages =
      match destination with
      | Module_context.Flat ->
          [
            `Representations;
            `Definitions;
            `Native_resources;
            `Public_resources;
            `Applications;
            `View_fields;
            `Fields;
            `Proof_definitions;
            `State;
            `Late_members;
            `Primitives;
            `Predicates;
            `Pure_functions;
            `Lemmas;
            `Logical_functions;
            `Procedures;
          ]
      | Module_context.Worker _ ->
          [
            `Primitives;
            `Pure_functions;
            `Representations;
            `Definitions;
            `Native_resources;
            `Public_resources;
            `Applications;
            `Fields;
            `State;
            `View_fields;
            `Proof_definitions;
            `Late_members;
            `Predicates;
            `Lemmas;
            `Logical_functions;
            `Procedures;
          ]
    in
    List.concat_map stages ~f:(function
      | `Representations -> representations
      | `Definitions -> emitted_assets destination definition_modules
      | `Native_resources -> native_resources
      | `Public_resources -> emitted_assets destination public_resource_members
      | `Applications -> applications
      | `View_fields -> ghost_fields
      | `Fields -> emitted_fields destination explicit_fields
      | `Proof_definitions -> emitted_assets destination definition_proof_modules
      | `State ->
          state_members group structure_member_lists
          @ state_members group pending_member_lists
          @ state_members group action_check_lists
      | `Late_members -> late_members
      | `Primitives -> primitive_members
      | `Predicates ->
          List.map (emitted_proofs destination predicate_members) ~f:R.Member.callable
      | `Pure_functions ->
          List.map (owned destination pure_funcs) ~f:(fun (_, member) ->
              R.Member.callable member)
      | `Lemmas ->
          List.map (emitted_proofs destination proof_lemma_members) ~f:R.Member.callable
      | `Logical_functions -> emitted_proofs destination logical_members
      | `Procedures -> List.map (owned destination procs) ~f:procedure_member)
  in
  let* generic_implementations =
    all generics ~f:(fun group ->
        let l = loc group.representative.template.mod_loc in
        let q = qualified_name ~loc:l in
        let* ra_data =
          all
            (List.filter_map private_ra_types ~f:(fun (plan, data) ->
                 Option.some_if (phys_equal plan.Generic_proofs.group group) data))
            ~f:(Datatypes.member types)
        in
        let destination = Module_context.Worker group in
        let native_resources =
          List.filter_map native_resource_members ~f:(fun (backend, member) ->
              Option.bind
                (List.find source.proof_resources ~f:(fun resource ->
                     String.equal backend resource.Source.resource_backend))
                ~f:(fun resource ->
                  Option.some_if
                    (Module_context.emits_owner module_contexts ~destination
                       resource.resource_scope)
                    member))
        in
        let members =
          emit_context_members destination ~at:l ~representations:ra_data
            ~native_resources ~applications:[] ~late_members:[]
        in
        let worker =
          R.Member.module_ ~loc:l
            ~params:
              (List.map (Generic_modules.parameter_groups group) ~f:(fun stage ->
                   (ident ~loc:l stage.parameter, q stage.interface))
              @
              if Option.is_some group.world then
                [ (ident ~loc:l "Layout", q (Option.value_exn group.world ^ ".Shape")) ]
              else [])
            (ident ~loc:l (Qualified_name.of_string group.name).name)
            members
        in
        match group.world with
        | None -> Ok worker
        | Some world ->
            let* layout_types =
              Result_layouts.symbolic layouts group ~owner:[ world; "Shape" ]
            in
            let proof_plan =
              List.find generic_proofs ~f:(fun plan ->
                  phys_equal plan.Generic_proofs.group group)
            in
            let model_types =
              Option.value_map proof_plan ~default:[] ~f:(fun plan ->
                  Generic_proofs.symbolic_models source plan ~owner:[ world; "Shape" ])
            in
            let parameter_types =
              Option.value_map proof_plan ~default:[] ~f:(fun plan ->
                  Generic_proofs.parameter_types ~world:true plan ~owner:(fun _ ->
                      [ world ]))
            in
            let layout_types = layout_types @ model_types in
            let environment =
              layout_types @ parameter_types
              @ List.concat_map (Generic_modules.parameter_groups group) ~f:(fun stage ->
                  Generic_modules.world_types stage ~owner:[ world ])
              @ types
            in
            let* data_members =
              all
                (List.filter layout_types ~f:(fun d -> Option.is_none d.Datatypes.heap))
                ~f:(Datatypes.member environment)
            in
            let* fields =
              all
                (List.concat_map layout_types ~f:(fun d ->
                     List.map (Option.value d.Datatypes.heap ~default:[]) ~f:(fun field ->
                         (d, field))))
                ~f:(fun (d, field) ->
                  let* typ =
                    Datatypes.typ environment ~at:d.Datatypes.at field.Datatypes.typ
                  in
                  let leaf = (Qualified_name.of_string field.raven_field).name in
                  Ok (Datatypes.field_member environment ~loc:l leaf typ field.typ))
            in
            let shape =
              R.Member.module_ ~loc:l ~interface:true (ident ~loc:l "Shape")
                (data_members @ fields)
            in
            let factory =
              R.Member.unit_factory ~loc:l
                ~implements:[ (q (world ^ ".Shape"), []) ]
                (ident ~loc:l "Fresh") []
            in
            Ok
              (R.Member.module_ ~loc:l
                 ~params:
                   (List.map (Generic_modules.type_slots group) ~f:(fun stem ->
                        (ident ~loc:l stem, R.Name.make ~loc:l ~path:[ "Library" ] "Type")))
                 (ident ~loc:l world)
                 (List.nth_exn generic_interfaces
                    (List.findi_exn generics ~f:(fun _ candidate ->
                         phys_equal candidate group)
                    |> fst)
                 @ [ shape; factory; worker ])))
  in
  let* generic_instances =
    all generics ~f:(fun group ->
        all group.applications ~f:(fun application ->
            let views =
              List.map application.source.parameters ~f:(fun parameter ->
                  List.find_exn checked_modules ~f:(fun view ->
                      phys_equal view.Checked_modules.binding
                        parameter.Module_inventory.argument))
            in
            let view_names = List.map views ~f:(fun view -> view.Checked_modules.name) in
            let l = loc application.source.argument.site.item_loc in
            let q = qualified_name ~loc:l in
            let* setup, worker, arguments =
              match group.world with
              | None -> Ok ([], group.name, view_names)
              | Some world ->
                  let* arguments =
                    all application.source.parameters ~f:(fun parameter ->
                        let concrete =
                          checked_raw_types types parameter.Module_inventory.argument
                        in
                        all parameter.argument.expected.signature_types
                          ~f:(fun (_, declaration) ->
                            let t =
                              Btype.newgenty
                                (Tconstr
                                   ( Path.Pident declaration.Typedtree.typ_id,
                                     [],
                                     ref Types.Mnil ))
                            in
                            Datatypes.typ concrete ~at:declaration.typ_loc t)
                        |> Result.bind ~f:(fun ordinary ->
                            all parameter.argument.expected.signature_ghost_modules
                              ~f:(fun (_, formal) ->
                                let resource = formal.Module_inventory.ghost_resource in
                                Datatypes.typ concrete ~at:resource.resource_at
                                  resource.resource_type)
                            |> Result.map ~f:(fun carriers -> ordinary @ carriers)))
                    |> Result.map ~f:List.concat
                  in
                  let selected =
                    if List.is_empty (Generic_modules.type_slots group) then
                      R.Member.alias ~loc:l (ident ~loc:l application.world) (q world)
                    else
                      R.Member.instance ~loc:l
                        ~def:(q world, arguments)
                        (ident ~loc:l application.world)
                        (q world)
                  in
                  let canonical =
                    List.find_exn group.applications ~f:(fun other ->
                        Path.same other.source.identity application.source.identity)
                  in
                  let fresh =
                    if phys_equal canonical application then
                      [
                        R.Member.unit_instance ~loc:l
                          (ident ~loc:l canonical.layout)
                          (q (application.world ^ ".Fresh"));
                      ]
                    else []
                  in
                  Ok
                    ( selected :: fresh,
                      application.world ^ "." ^ (Qualified_name.of_string group.name).name,
                      view_names @ [ canonical.layout ] )
            in
            Ok
              ( application.source.argument,
                setup,
                R.Member.instance ~loc:l
                  ~def:
                    ( q worker,
                      List.map arguments ~f:(fun n -> R.Type.named ~loc:l (q n) []) )
                  (ident ~loc:l application.name)
                  (q worker) )))
  in
  let generic_instances = List.concat generic_instances in
  let _, native_blocks =
    List.fold (List.zip_exn checked_modules checked_module_members) ~init:([], [])
      ~f:(fun (emitted, blocks) (view, members) ->
        let binding = view.Checked_modules.binding in
        let captured =
          List.exists generics ~f:(fun group ->
              List.exists group.Generic_modules.captures ~f:(fun stage ->
                  List.exists stage.applications ~f:(fun application ->
                      phys_equal application.source.argument binding)))
        in
        let final =
          List.exists generics ~f:(fun group ->
              List.exists group.Generic_modules.applications ~f:(fun application ->
                  phys_equal application.source.argument binding))
        in
        if captured && not final then (emitted, blocks)
        else
          let attached =
            List.concat_map generics ~f:(fun group ->
                List.concat_map group.Generic_modules.applications ~f:(fun application ->
                    if not (phys_equal application.source.argument binding) then []
                    else
                      List.filter_map (List.drop_last_exn application.source.parameters)
                        ~f:(fun parameter ->
                          let argument = parameter.Module_inventory.argument in
                          Option.some_if
                            (not (List.mem emitted argument ~equal:phys_equal))
                            argument)))
          in
          let rec attach (emitted, attached) argument =
            if List.mem emitted argument ~equal:phys_equal then (emitted, attached)
            else
              let view =
                List.find_exn checked_modules ~f:(fun view ->
                    phys_equal view.Checked_modules.binding argument)
              in
              let dependency =
                Option.bind view.target ~f:(fun target ->
                    List.find checked_modules ~f:(fun candidate ->
                        String.equal candidate.Checked_modules.name target))
              in
              let emitted, attached =
                Option.value_map dependency ~default:(emitted, attached)
                  ~f:(fun dependency -> attach (emitted, attached) dependency.binding)
              in
              (argument :: emitted, argument :: attached)
          in
          let _, attached = List.fold attached ~init:(emitted, []) ~f:attach in
          let attached = List.rev attached in
          let attached_members =
            List.concat_map attached ~f:(fun argument ->
                snd
                  (List.find_exn (List.zip_exn checked_modules checked_module_members)
                     ~f:(fun (view, _) ->
                       phys_equal view.Checked_modules.binding argument)))
          in
          let prefix =
            List.concat_map
              (List.zip_exn generics
                 (List.zip_exn generic_interfaces generic_implementations))
              ~f:(fun (group, (interface, implementation)) ->
                if phys_equal group.representative.argument binding then
                  match group.Generic_modules.world with
                  | None -> interface @ [ implementation ]
                  | Some _ -> [ implementation ]
                else [])
          in
          let instances =
            List.filter_map generic_instances ~f:(fun (argument, _, instance) ->
                Option.some_if (phys_equal argument binding) instance)
          in
          let publications =
            List.filter_map !publication_members ~f:(fun (owner, member) ->
                Option.some_if
                  (phys_equal owner binding || List.mem attached owner ~equal:phys_equal)
                  (R.Member.callable member))
          in
          let setup =
            List.concat_map generic_instances ~f:(fun (argument, setup, _) ->
                if phys_equal argument binding then setup else [])
          in
          List.iter generics ~f:(fun group ->
              List.iter group.Generic_modules.applications ~f:(fun application ->
                  if
                    phys_equal application.source.argument binding
                    && Option.is_some group.world
                  then available_layouts := application.layout :: !available_layouts));
          let declarations = take_declarations () in
          List.iter generics ~f:(fun group ->
              List.iter group.Generic_modules.applications ~f:(fun application ->
                  if phys_equal application.source.argument binding then
                    available_layouts := application.name :: !available_layouts));
          let after_instances = take_declarations () in
          ( (binding :: attached) @ emitted,
            (prefix @ setup @ declarations @ publications @ attached_members @ members
           @ instances @ after_instances)
            :: blocks ))
  in
  let native_modules = List.concat (List.rev native_blocks) in

  let file_start = { Lexing.dummy_pos with pos_fname = source.file } in
  let start = R.Loc.make file_start file_start in
  let ref_fields = List.map !refs ~f:snd in
  let root_members =
    emit_context_members Module_context.Flat ~at:start ~representations:[]
      ~native_resources:deferred_native_resource_members ~applications:native_modules
      ~late_members:(List.concat_map !pending_declarations ~f:snd @ ref_fields)
  in
  Ok
    ( R.Program.make ~loc:start
        (Prelude.members
        @ (if
             shared.dynamic_indices
             || List.exists generic_shared ~f:(fun (_, shared) -> shared.dynamic_indices)
           then Indexed_initialization.members
           else [])
        @ imported_resource_members @ modules @ library_modules @ root_members),
      !origins )
