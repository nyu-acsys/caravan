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

(** The conjuncts of [terms] that make a variable a field of a value, [x = g.f] or
    [g.f = x]: the variable, the field and the value's name. *)
let field_equations (terms : S.term list) =
  List.filter_map (List.concat_map terms ~f:conjuncts) ~f:(fun t ->
      match spine t [] with
      | { term_desc = Tvar (Qid { pid_str = "="; _ }); _ }, [ a; b ] ->
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
  linearizes : string list;
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
  helped : string;  (** The function whose calls wait. *)
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
  role : string;
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

type structure = {
  invariant : string;
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
let member_name st suffix = st.invariant ^ "_" ^ suffix

let module_name st suffix = String.capitalize st.invariant ^ "_" ^ suffix

(** The names of the members generated for the pending field [p] of [st]. *)
let pending_name st (p : pending) suffix = member_name st (p.pending_field ^ "_" ^ suffix)

type past = { inv : string; field : string; element : S.term }
(** A fact about an earlier state of a structure, [past (mem e s.f)]: [e] was in the field
    [f], owned by index, of a state of the invariant [inv], which a snapshot of its
    history and a position in [f] witness. *)

(** [t] as a fact about an earlier state, if it is one, of the structures [structures]. *)
let past_of structures (t : S.term) =
  match spine (S.chain t) [] with
  | { term_desc = Tvar (Qid { pid_str = "past"; _ }); _ }, [ fact ] ->
      begin match spine (S.chain fact) [] with
      | ( { term_desc = Tvar (Qid { pid_str = "mem"; _ }); _ },
          [
            element;
            {
              term_desc =
                Tfield
                  ( { term_desc = Tvar (Qid { pid_str = s; _ }); _ },
                    Qid { pid_str = f; _ } );
              _;
            };
          ] ) ->
          Option.bind
            (List.find structures ~f:(fun st -> String.equal st.state s))
            ~f:(fun st ->
              Option.some_if
                (List.Assoc.mem st.chains f ~equal:String.equal)
                { inv = st.invariant; field = f; element })
      | _ -> None
      end
  | _ -> None

(** The state of the growing fields [values] of [st], as the history holds it. *)
let state_of ~loc:l st values =
  R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ module_name st "state" ] "state") values

(** That the snapshot [snapshot] of [st]'s history, on the structure [structure], has the
    value [e] at the position [k] of its field [field]. *)
let past_fact ~loc:l st ~structure ~field ~snapshot ~k e =
  let qn m x = R.Name.make ~loc:l ~path:[ m ] x in
  let entries = R.Expr.field ~loc:l snapshot (R.Name.make ~loc:l field) in
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
  anchors : (string * (string * R.Type.t * R.Expr.t option) list) list;
      (** The ghost fields of the views and histories, by the field whose allocation
          allocates them, the field of the structure's reference, with their initial
          values: arbitrary for views. *)
}
(** The shared structures of a program: invariants and views. *)

let no_shared = { persistent = []; views = []; structures = []; anchors = [] }

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

type lemma_signature = {
  lemma_raven : string;
  lemma_inputs : Types.type_expr list;
  lemma_outputs : Types.type_expr list;
}

type proof_support = {
  resources : Source.proof_resource list;
  ghost_fields : Source.proof_field list;
  logical_functions : (string * lemma_signature) list;
}

let empty_proof_support = { resources = []; ghost_fields = []; logical_functions = [] }

type context = {
  types : Datatypes.t list;
  refs : (string * R.Member.t) list ref;
      (** The fields of the ref cells and atomics used so far, by their names, with their
          declarations. *)
  primitives : (string * R.Member.t) list ref;
      (** The atomic operations used so far, by their names (see {!Primitives}). *)
  names : Names.t;
  functions : (string * string) list;
      (** The top-level functions, by the unique name of their OCaml identifier. *)
  pasts : (string * (string * string * int) list) list;
      (** The facts about earlier states that procedures require, by their names: the
          invariant, the field, and the position of the parameter that was in it. *)
  past_returns :
    (string * (string * string * (R.Expr.t list -> R.Expr.t option)) list) list;
      (** The facts about earlier states that procedures ensure, by their names, each
          witnessed by two ghost results: the invariant, the field, and the entry, given
          the arguments, if it is known. *)
  lifted : (string * (int * Ident.t list * string option)) list;
      (** The lifted local functions, by their procedures' names, with the number of
          parameters of the function they continue, which they take first, the variables
          of their context they use, which they take next, and the function's name. *)
  ghost_args : (string * (int * string) option list) list;
      (** The ghost parameters of procedures, by their names: for each, the position of a
          parameter that a precondition makes a field of it, with the field, as [tail] in
          [requires tail = q.tail], by which calls find the ghost argument. *)
  mutable fields_of : (string * (string * R.Expr.t)) list;
      (** The variables known to be fields of values, by their Raven names: the field and
          the value, as [tail] of [q] after [let push { tail; _ } value]. *)
  libraries : (Ident.t * string) list;
      (** The modules of the libraries, with their names: trusted Raven modules. *)
  mutable formals : R.Expr.t list;
      (** The procedure's parameters, of which a lifted local function that continues it,
          or that it continues too, takes the first. *)
  origins : origin list ref;
  annotations : Annotation.t list;  (** Those of the file, as loops' invariants. *)
  proof_lemmas : (string * lemma_signature) list;
  proof_support : proof_support;
  predicate_bodies : (string * S.term) list;
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
let field_type ctx (t : Types.type_expr) label =
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
  R.Stmt.assign ~loc:l [ R.Expr.field ~loc:l r (name ~loc:l field) ] (R.Stmt.expr_rhs v)

(** The name of [p] if it is a value of the standard library's toplevel. *)
let stdlib_name (p : Path.t) =
  match p with
  | Pdot (Pident m, x) when String.equal (Ident.name m) "Stdlib" -> Some x
  | _ -> None

(** The name of [p] if it is a value of [Stdlib.Atomic]. *)
let atomic_name (p : Path.t) =
  match p with
  | Pdot (Pdot (Pident m, "Atomic"), x) when String.equal (Ident.name m) "Stdlib" ->
      Some x
  | Pdot (Pident m, x) when String.equal (Ident.name m) "Stdlib__Atomic" -> Some x
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
  | "=" | "==" -> Some Eq
  | "<>" | "!=" -> Some Neq
  | "<" -> Some Lt
  | "<=" -> Some Leq
  | ">" -> Some Gt
  | ">=" -> Some Geq
  | "&&" | "/\\" -> Some And
  | "||" | "\\/" -> Some Or
  | "->" -> Some Impl
  | "<->" -> Some Iff
  | _ -> None

(** The name of [q] in contracts: [x], or [M.x] for a name of a library's module. *)
let qualid_key : S.qualid -> string = function
  | Qid x -> x.pid_str
  | Qdot (Qid m, x) -> m.pid_str ^ "." ^ x.pid_str
  | Qdot (_, x) -> x.pid_str

(** The Raven name of the name [x] of a contract, qualified as a library's, [M.x]. *)
let qualified_name ~loc x =
  match String.lsplit2 x ~on:'.' with
  | Some (m, y) -> R.Name.make ~loc ~path:[ m ] y
  | None -> R.Name.make ~loc x

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

let resource_operation env = function
  | S.Qdot (Qid m, f) ->
      Option.bind
        (List.find env.ctx.proof_support.resources ~f:(fun r ->
             String.equal r.Source.resource_name m.pid_str))
        ~f:(fun resource ->
          List.find_map resource.resource_operations ~f:(fun (op, inputs, result) ->
              Option.some_if (String.equal op f.pid_str)
                {
                  lemma_raven = m.pid_str ^ "." ^ op;
                  lemma_inputs = inputs;
                  lemma_outputs = [ result ];
                }))
  | _ -> None

let logical_signature env q =
  match q with
  | S.Qid id when List.Assoc.mem env.vars id.pid_str ~equal:String.equal -> None
  | _ ->
      begin match resource_operation env q with
      | Some _ as signature -> signature
      | None ->
          List.Assoc.find env.ctx.proof_support.logical_functions (qualid_key q)
            ~equal:String.equal
      end

let ghost_projection env t =
  match spine t [] with
  | ( { S.term_desc = Tvar (Qdot (Qid m, op)); _ },
      [ { term_desc = Tvar (Qid field); _ }; owner ] )
    when String.equal m.pid_str "Ghost" && String.equal op.pid_str "at" ->
      Option.bind
        (List.find env.ctx.proof_support.ghost_fields ~f:(fun f ->
             String.equal f.Source.field_name field.pid_str))
        ~f:(fun descriptor ->
          Option.some_if
            (not (List.Assoc.mem env.vars field.pid_str ~equal:String.equal))
            (descriptor, owner))
  | _ -> None

let ghost_field_name (field : Source.proof_field) = "proof$" ^ field.field_name

let is_ghost_fpu t =
  match spine t [] with
  | { S.term_desc = Tvar (Qdot (Qid m, op)); _ }, _ ->
      String.equal m.pid_str "Ghost" && String.equal op.pid_str "fpu"
  | _ -> false

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
  let known x =
    List.Assoc.mem env.vars x ~equal:String.equal
    || List.Assoc.mem env.funcs x ~equal:String.equal
    || List.exists env.ctx.proof_support.ghost_fields ~f:(fun f ->
        String.equal f.Source.field_name x)
    || List.mem
         [ "own"; "not"; "max_int"; "min_int"; "mod"; "length"; "last"; "drop"; "take" ]
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
  (* The parameter types of the predicates that [t] passes names to. *)
  let rec passed (t : S.term) =
    let head, args = spine t [] in
    let here =
      match head.term_desc with
      | Tvar q ->
          begin match
            List.Assoc.find env.ctx.preds (qualid_key q) ~equal:String.equal
          with
          | Some (_, types) when List.length types = List.length args ->
              List.filter_map (List.zip_exn args types) ~f:(fun ((a : S.term), t) ->
                  match a.term_desc with
                  | Tvar (Qid { pid_str = v; _ }) -> Some (v, t)
                  | _ -> None)
          | _ -> []
          end
      | _ -> []
    in
    here
    @
    match t.term_desc with
    | Tapply (a, b) | Tinfix (a, _, b) -> passed a @ passed b
    | Tif (a, b, c) -> passed a @ passed b @ passed c
    | Tattr (_, t) | Tcast (t, _) -> passed t
    | _ -> []
  in
  let owned = List.concat_map terms ~f:owned @ List.concat_map terms ~f:passed in
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

(** The formula [t] of a contract. *)
let rec formula (env : env) (t : S.term) : (R.Expr.t, error) Result.t =
  let at = t.term_loc in
  let l = loc at in
  match t.term_desc with
  | Ttrue -> Ok (R.Expr.bool ~loc:l true)
  | Tfalse -> Ok (R.Expr.bool ~loc:l false)
  | Tconst (Pconst_integer (n, None)) -> Ok (R.Expr.int ~loc:l (Int.of_string n))
  | Tconst _ -> unsupported at "This constant"
  | Tvar (Qid { pid_str = x; _ }) when is_constructor x -> constructor env t []
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
      let scrutinee_type =
        match scrutinee.term_desc with
        | Tvar (Qid { pid_str = x; _ }) ->
            List.Assoc.find env.var_types x ~equal:String.equal
        | _ -> None
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
          Ok (R.Expr.field ~loc:l r (name ~loc:l label))
      end
  | Tfield (_, Qdot _) -> unsupported at "A qualified field"
  | Tlet (pattern, value, body) when env.logical_definition ->
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
  | Tlet _ | Told _ -> unsupported at "This formula"

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
  let literal = list_literal in
  let is_sequence ty =
    match Datatypes.desc env.data ty with
    | Tconstr (p, [ _ ], _) ->
        Option.exists (Datatypes.find env.data p) ~f:Datatypes.is_sequence
    | _ -> false
  in
  match (Option.map expected ~f:is_sequence, literal t) with
  | Some true, Some elements ->
      let* elements = all elements ~f:(formula env) in
      Ok (R.Expr.seq ~loc:(loc t.term_loc) elements)
  | _ -> formula env t

(** The OCaml type of [t], where it is known: a variable's, or a sequence's slice or
    concatenation. *)
and term_type env (t : S.term) =
  match (t.term_desc, spine t []) with
  | Tcast (_, ty), _ -> Result.ok (Source.ocaml_type env.ctx.env ~at:t.term_loc ty)
  | Tconst (Pconst_integer _), _ -> Some Predef.type_int
  | (Ttrue | Tfalse), _ -> Some Predef.type_bool
  | Tcomprehension ((_, ty), _), _ ->
      Result.ok
        (Source.ocaml_type env.ctx.env ~at:t.term_loc
           (S.PTtyapp (Qid (S.mk_id ~loc:t.term_loc "set"), [ ty ])))
  | _, ({ term_desc = Tvar q; _ }, _) when Option.is_some (logical_signature env q) ->
      List.hd (Option.value_exn (logical_signature env q)).lemma_outputs
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
             match Datatypes.desc env.data ty with
             | Tconstr (p, [], _) ->
                 Option.bind (Datatypes.find env.data p) ~f:(fun d ->
                     match d.ctors with
                     | [ c ] ->
                         List.Assoc.find
                           (List.zip_exn c.fields c.args)
                           f ~equal:String.equal
                     | _ -> None)
             | _ -> None))
  | _, ({ term_desc = Tvar (Qid { pid_str = "([])" | "last"; _ }); _ }, s :: _) ->
      (* An entry of a sequence. *)
      begin match Option.map (term_type env s) ~f:(Datatypes.desc env.data) with
      | Some (Tconstr (_, [ elt ], _)) -> Some elt
      | _ -> None
      end
  | _ -> None

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

(** The application [t] of an operator or a constructor. *)
and application env (t : S.term) =
  let at = t.term_loc in
  let l = loc at in
  let head, args = spine t [] in
  match (head.term_desc, args) with
  | Tvar (Qid id), _ when List.Assoc.mem env.vars id.pid_str ~equal:String.equal ->
      error head.term_loc "A local proof value cannot be called as a logical function"
  | Tvar q, args when Option.is_some (logical_signature env q) ->
      logical_application env ~at (Option.value_exn (logical_signature env q)) args
  | Tvar q, args when Option.is_some (collection_builtin env q) ->
      collection_application env ~at (Option.value_exn (collection_builtin env q)) args
  | Tvar (Qid { pid_str = "not"; _ }), [ a ] ->
      let* a = formula env a in
      Ok (R.Expr.not_ ~loc:l a)
  | Tvar (Qid { pid_str = "own"; _ }), [ location; v ] ->
      let expected = location_type env location in
      let* location = location_of env location in
      let* v = expected_formula env expected v in
      Ok (R.Expr.own ~loc:l [ location; v ])
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
  | Tvar (Qid { pid_str = op; pid_fixity = Infix; _ }), [ a; b ] ->
      begin match spec_binop op with
      | None -> unsupported at (Printf.sprintf "The operator %s" op)
      | Some op -> (
          (* A literal compared with a sequence is one. *)
          let a_type = term_type env a
          and b_type = term_type env b in
          let* a = expected_formula env b_type a in
          let* b = expected_formula env a_type b in
          match op with
          | Div -> Ok (prelude_call ~loc:l Prelude.div [ a; b ])
          | Mod -> Ok (prelude_call ~loc:l Prelude.mod_ [ a; b ])
          | _ -> Ok (R.Expr.binary ~loc:l op a b))
      end
  | Tvar (Qid { pid_str = c; _ }), _ when is_constructor c -> constructor env t args
  | Tvar q, _ :: _ when List.Assoc.mem env.funcs (qualid_key q) ~equal:String.equal ->
      let f = qualid_key q in
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

and logical_application env ~at signature args =
  let l = loc at in
  if List.length args <> List.length signature.lemma_inputs then
    error at
      (Printf.sprintf "%s expects %d arguments" signature.lemma_raven
         (List.length signature.lemma_inputs))
  else
    let* args =
      all (List.zip_exn signature.lemma_inputs args) ~f:(fun (ty, value) ->
          let* () =
            Source.check_logical_expression env.ctx.env
              ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types ~expected:ty
              value
          in
          let* () =
            match term_type env value with
            | Some actual when not (Ctype.is_equal env.ctx.env false [ ty ] [ actual ]) ->
                error value.term_loc
                  (Stdlib.Format.asprintf "Expected logical type %a but found %a"
                     Printtyp.type_expr ty Printtyp.type_expr actual)
            | _ -> Ok ()
          in
          let* value = expected_formula env (Some ty) value in
          let* raven_type = typ env.ctx ~at ty in
          Ok (R.Expr.annotated value raven_type))
    in
    let n = qualified_name ~loc:l signature.lemma_raven in
    if String.is_suffix signature.lemma_raven ~suffix:".id" then Ok (R.Expr.var ~loc:l n)
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
  | Pconstr (Qid { pid_str = c; _ }, arg), Tconstr (path, args, _) -> begin
      let arg_types =
        match (c, args) with
        | "::", [ elt ] when Path.same path Predef.path_list -> [ elt; t ]
        | "Some", [ elt ] when Path.same path Predef.path_option -> [ elt ]
        | _ ->
            begin match Datatypes.find env.data path with
            | Some d ->
                Option.value_map
                  (List.find d.ctors ~f:(fun ctor -> String.equal ctor.ocaml c))
                  ~default:[]
                  ~f:(fun ctor -> ctor.args)
            | None -> []
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
      Ok (R.Expr.field ~loc:l owner (name ~loc:l (ghost_field_name field)))
  | None -> (
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
              | Some field, _ -> Ok (R.Expr.field ~loc:l r (name ~loc:l field))
              | None, Some atomic -> begin
                  (* An atomic that an immutable record holds. *)
                  let atomic_ref = R.Expr.field ~loc:l r (name ~loc:l label) in
                  let* field = field_of_type env.ctx ~at atomic "" in
                  match field with
                  | Some field -> Ok (R.Expr.field ~loc:l atomic_ref (name ~loc:l field))
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
          | Some field -> Ok (R.Expr.field ~loc:l r (name ~loc:l field))
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
              Ok (R.Expr.field ~loc:l r (name ~loc:l field))
          | None ->
              unsupported at
                "This location, other than a field of a variable or an atomic,"
        end)

(** The constructor [t], or the application [t] of a constructor to [args]. *)
and constructor env (t : S.term) args =
  let at = t.term_loc in
  let l = loc at in
  let head, _ = spine t [] in
  let c_name = match head.term_desc with Tvar (Qid id) -> id.pid_str | _ -> "" in
  match Datatypes.find_ctor env.data c_name with
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
  | Pconstr (Qid { pid_str = c_name; _ }, arg) ->
      begin match Datatypes.find_ctor env.data c_name with
      | None -> error at (Printf.sprintf "Unbound constructor %s" c_name)
      | Some (_, c) ->
          let tuple (p : S.pat) =
            match p.pat_desc with Ptuple ps -> Some ps | _ -> None
          in
          let* args = ctor_args ~at (List.length c.fields) (Option.to_list arg) ~tuple in
          let fields =
            List.map c.fields ~f:(fun f -> R.Expr.field ~loc:l v (name ~loc:l f))
          in
          let* conds, binds = components args fields in
          Ok (conjoin (Some (R.Expr.is_ ~loc:l v (ident ~loc:l c.raven)) :: conds), binds)
      end
  | Pconstr (Qdot _, _) -> unsupported at "A qualified constructor"

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
        | Pconstr (Qid { pid_str = c_name; _ }, arg) -> begin
            let args =
              match arg with
              | None -> Some []
              | Some { pat_desc = Ptuple ps; _ } -> Option.all (List.map ps ~f:flat_arg)
              | Some p -> Option.map (flat_arg p) ~f:(fun a -> [ a ])
            in
            match (Datatypes.find_ctor env.data c_name, args) with
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
  | Tvar (Qid id) ->
      begin match List.Assoc.find env.ctx.proof_lemmas id.pid_str ~equal:String.equal with
      | None -> error id.pid_loc (Printf.sprintf "Unknown lemma %s" id.pid_str)
      | Some signature ->
          if List.length args <> List.length signature.lemma_inputs then
            error t.term_loc
              (Printf.sprintf "Lemma %s expects %d arguments" id.pid_str
                 (List.length signature.lemma_inputs))
          else
            let* args =
              all (List.zip_exn signature.lemma_inputs args) ~f:(fun (ty, arg) ->
                  expected_formula env (Some ty) arg)
            in
            Ok
              ( R.Expr.call ~loc:(loc t.term_loc)
                  (name ~loc:(loc t.term_loc) signature.lemma_raven)
                  args,
                signature.lemma_outputs )
      end
  | _ -> error t.term_loc "Expected a lemma applied to its arguments"

let predicate_use env ~unfold t witnesses make =
  let head, args = spine t [] in
  match head.term_desc with
  | Tvar (Qid { pid_str = p; _ }) when List.Assoc.mem env.ctx.preds p ~equal:String.equal
    ->
      let raven, _ = List.Assoc.find_exn env.ctx.preds p ~equal:String.equal in
      let* args = all args ~f:(formula env) in
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
      Ok (make ~loc:l ?witnesses:(Some witnesses) (name ~loc:l raven) args)
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

let proof_signature env (t : S.term) =
  let head, _ = spine t [] in
  match head.term_desc with
  | Tvar (Qid id) when not (List.Assoc.mem env.vars id.pid_str ~equal:String.equal) ->
      List.Assoc.find env.ctx.proof_lemmas id.pid_str ~equal:String.equal
  | _ -> None

let ghost_fpu env t =
  let _, args = spine t [] in
  match args with
  | [ location; before; after ] ->
      begin match ghost_projection env location with
      | None -> error location.term_loc "Ghost.fpu needs a declared ghost field location"
      | Some (field, _) ->
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
  match t.term_desc with
  | Tcast (_, ty) ->
      let* ty = Source.ocaml_type env.ctx.env ~at:t.term_loc ty in
      Ok (Some ty)
  | Tconst (Pconst_integer _) -> Ok (Some Predef.type_int)
  | Ttrue | Tfalse -> Ok (Some Predef.type_bool)
  | Tapply ({ term_desc = Tvar (Qid { pid_str = "Some"; _ }); _ }, value) ->
      let* ty = proof_value_type env value in
      Ok (Option.map ty ~f:(fun ty -> Ctype.newconstr Predef.path_option [ ty ]))
  | Ttuple ts ->
      let* ts = all ts ~f:(proof_value_type env) in
      Ok
        (Option.map (Option.all ts) ~f:(fun ts ->
             Btype.newgenty (Ttuple (List.map ts ~f:(fun ty -> (None, ty))))))
  | _ -> Ok (term_type env t)

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
  | Tvar (Qid predicate)
    when List.Assoc.mem env.ctx.preds predicate.pid_str ~equal:String.equal ->
      begin match
        List.Assoc.find env.ctx.predicate_bodies predicate.pid_str ~equal:String.equal
      with
      | None -> Ok None
      | Some body ->
          let bindings = predicate_existentials body in
          let* types =
            all witnesses ~f:(fun (witness : S.id) ->
                match
                  List.filter bindings ~f:(fun (id, _) ->
                      String.equal id.S.pid_str witness.pid_str)
                with
                | [] ->
                    error witness.pid_loc
                      (Printf.sprintf "Predicate %s has no existential named %s"
                         predicate.pid_str witness.pid_str)
                | [ (_, Some ty) ] ->
                    let* ty = Source.ocaml_type env.ctx.env ~at:witness.pid_loc ty in
                    Ok (Some ty)
                | [ (_, None) ] ->
                    error witness.pid_loc "An existential variable needs a type"
                | _ ->
                    error witness.pid_loc
                      (Printf.sprintf "Existential name %s is ambiguous in predicate %s"
                         witness.pid_str predicate.pid_str))
          in
          Ok (Some types)
      end
  | _ -> error t.term_loc "Expected a predicate applied to its arguments"

let rec proof_result_types env (body : S.proof_expr) =
  match body.proof_desc with
  | Proof_value t when is_ghost_fpu t -> Ok (Some [])
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
            let* types =
              proof_result_types { env with var_types = types @ env.var_types } body
            in
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
  | Proof_value t ->
      begin match proof_signature env t with
      | Some _ ->
          let* call, outputs = lemma_call env t in
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
      let* rhs =
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
      let* rest = proof_expression env targets rest in
      Ok (List.concat_map declarations ~f:(fun (_, _, stmts) -> stmts) @ rhs @ rest)
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

(** Ghost annotations supplement the automatic path without declaring mutable state. *)
let ghost ctx ~(after : Lexing.position) ~(before : Lexing.position) =
  let between (a : Annotation.t) =
    a.loc.loc_start.pos_cnum >= after.pos_cnum
    && a.loc.loc_end.pos_cnum <= before.pos_cnum
    && Poly.equal (Annotation.kind a) Annotation.Ghost
  in
  let* blocks = all (List.filter ctx.annotations ~f:between) ~f:Annotation.ghost_stmts in
  let* stmts = all (List.concat blocks) ~f:(proof_statement (scope_env ctx)) in
  Ok stmts

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
  | [] -> Ok { S.invariants = []; loop_variant = [] }
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
  let* free = free_typed env spec.invariants ~at in
  let env =
    List.fold free ~init:env ~f:(fun env (x, raven, t, _, _) ->
        { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
  in
  let* invariants = all spec.invariants ~f:(formula env) in
  (* The values that the invariants own, by the Raven names of their references and
     fields. *)
  let* reads =
    all (List.concat_map spec.invariants ~f:owned_names) ~f:(fun (x, label, v) ->
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
                      fun ~loc e -> R.Expr.field ~loc e (name ~loc label) )
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
  let env =
    bind (scope_env ctx) st.state
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
  let env =
    bind (scope_env ctx) st.state
      (State (List.map2_exn st.fields values ~f:(fun (f, _, _, t, _) e -> (f, (e, t)))))
  in
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
      (R.Name.make ~loc:l ~path:[ module_name st "state" ] "state")
      (grown st values)
  in
  let lemma f args = R.Stmt.call ~loc:l (R.Expr.call ~loc:l (name ~loc:l f) args) in
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
                (name ~loc:l inv) args;
            ]
          @ kept
      | false, None -> [ R.Stmt.unfold ~loc:l (name ~loc:l inv) args ]
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
            [ R.Stmt.fold ~loc:l ~witnesses (name ~loc:l inv) args ]
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
                       (R.Name.make ~loc:l ~path:[ module_name st "state" ] "T")
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
                 (name ~loc:l (member_name st "snapshot"))
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
        [ R.Expr.field ~loc (anchored ctx ~loc ~pred structure) (name ~loc field) ]
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
                   ~loc:l ~pred (name ~loc:l raven) (inputs @ [ value ])))
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
      Ok (R.Expr.field ~loc:l r (name ~loc:l label))
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
      match Datatypes.find_ctor env.data c with
      | Some (_, ctor) when List.length ctor.fields = List.length args ->
          List.concat
            (List.map2_exn args ctor.fields ~f:(fun a f ->
                 bind_params env st opened params a
                   (R.Expr.field ~loc:l actual (R.Name.make ~loc:l f))))
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
let named_action ctx a =
  List.find_map ctx.shared.structures ~f:(fun st ->
      List.find st.actions ~f:(fun act -> String.equal act.action a))

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
let decision_env ctx st (opened : opened) (p : S.pat) value =
  let env =
    bind (scope_env ctx) st.state
      (State
         (List.map2_exn st.fields opened.values ~f:(fun (f, _, _, t, _) v -> (f, (v, t)))))
  in
  match p.pat_desc with
  | Pid x -> Ok (bind env x.pid_str (Value value))
  | Pwild -> Ok env
  | _ -> unsupported p.pat_loc "A pattern other than a variable, before a choice,"

(** The statements of the step at [at] of the function with the update [au], whose result
    [value] matches [p]: the invariants are open, and [outcome] linearizes the function or
    leaves it to be helped, registered on a pending field. *)
let decide ctx (au : au) ~(at : Location.t) ~value (p : S.pat) (outcome : S.outcome) =
  let l = loc at in
  let var x = R.Expr.var ~loc:l (name ~loc:l x) in
  let* st, args, opened =
    match open_pending_structure ctx with
    | Some found -> Ok found
    | None -> error at "A step that may wait without a structure with pending calls"
  in
  let* env = decision_env ctx st opened p value in
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
        let field f = name ~loc:l (pending_name st pending f) in
        let lemma f es = R.Stmt.call ~loc:l (R.Expr.call ~loc:l (name ~loc:l f) es) in
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
               (name ~loc:l (pending_name st pending "registration"))
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
               (name ~loc:l inv) args;
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
  let registration = name ~loc:l (pending_name st r.pending "registration") in
  let retired = name ~loc:l (pending_name st r.pending "retired") in
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
let linearize ?step ?value ctx ~at
    (how :
      [ `Commit | `Abort | `Cas | `Returning of string | `Decide of S.pat * S.outcome ])
    access =
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
          let* decision = decide ctx au ~at ~value p o in
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
            "This function waits to be helped: the next step collects its result, as (*@ \
             returning Nil -> commit true *)"
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
                      List.mem p.performed.linearizes au.role ~equal:String.equal)
                in
                begin match (linearizing, au.performing) with
                | _, Some _ | [], None -> Ok []
                | [ (p, condition) ], None ->
                    au.performing <- Some (p, Some condition);
                    Ok []
                | _ :: _ :: _, None ->
                    error at
                      "This step may perform several actions that linearize the function"
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
        | Some init -> ([], (name ~loc:l view, Some init))
        | None ->
            let x = Names.fresh ctx.names "view" in
            ( R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x),
              (name ~loc:l view, Some (R.Expr.var ~loc:l (name ~loc:l x))) ))
  in
  (List.concat_map allocated ~f:fst, List.map allocated ~f:snd)

(** The statements evaluating [e], and the value of [e] after them; [tail] if the value is
    the function's result. *)
let rec expr ?(tail = false) (ctx : context) (e : Typedtree.expression) :
    (R.Stmt.t list * R.Expr.t, error) Result.t =
  let at = e.exp_loc in
  let l = loc at in
  match e.exp_desc with
  | Texp_ident (Pident id, _, _) -> (
      match Names.find ctx.names id with
      | Some x -> Ok ([], R.Expr.var ~loc:l (name ~loc:l x))
      | None -> unsupported at "A function used as a value")
  | Texp_ident (Pdot (Pident m, x), _, _)
    when List.Assoc.mem ctx.libraries m ~equal:Ident.same ->
      (* A value of a library, which its module gives by a function. *)
      Ok
        ( [],
          R.Expr.call ~loc:l
            (R.Name.make ~loc:l
               ~path:[ List.Assoc.find_exn ctx.libraries m ~equal:Ident.same ]
               x)
            [] )
  | Texp_ident (p, _, _) -> (
      match stdlib_name p with
      | Some "max_int" -> Ok ([], R.Expr.int ~loc:l Prelude.max_int)
      | Some "min_int" -> Ok ([], R.Expr.int ~loc:l Prelude.min_int)
      | _ -> unsupported at "This identifier")
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
          let init =
            R.Stmt.new_rhs
              (List.map2_exn fields args ~f:(fun f v -> (name ~loc:l f, Some v))
              @ view_args)
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
          let* typ = typ ctx ~at e.exp_type in
          let x = Names.fresh ctx.names "tmp" in
          let read = R.Stmt.expr_rhs (R.Expr.field ~loc:l v (name ~loc:l field)) in
          Ok
            ( stmts @ R.Stmt.local ~loc:l ~typ ~init:read (ident ~loc:l x),
              R.Expr.var ~loc:l (name ~loc:l x) )
      | Some (field, false) -> Ok (stmts, R.Expr.field ~loc:l v (name ~loc:l field))
      | None -> unsupported at "This field"
    end
  | Texp_setfield (record, _, label, value) -> begin
      let* value_stmts, value = expr ctx value in
      let* record_stmts, record = expr ctx record in
      let* field = field_of_label ctx ~at label in
      match field with
      | Some (field, true) ->
          Ok
            ( value_stmts @ record_stmts @ [ write ~loc:l record field value ],
              unit_value ~loc:l )
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
    when List.Assoc.mem ctx.functions (Ident.unique_name id) ~equal:String.equal ->
      (* A local function, lifted to the top level. *)
      expr ~tail ctx rest
  | Texp_let (Nonrecursive, bindings, body) ->
      (* The bound expressions are evaluated before any of their variables is bound. *)
      let* evaluated =
        all bindings ~f:(fun (vb : Typedtree.value_binding) ->
            let polarity = cas_polarity ctx vb.vb_expr in
            let read = is_read_value ctx vb.vb_expr in
            let* stmts, v = expr ctx vb.vb_expr in
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
            let* cond, binds = pattern ctx vb.vb_pat v in
            match cond with
            | Some _ ->
                unsupported vb.vb_pat.pat_loc "A refutable pattern in a let binding"
            | None ->
                all binds ~f:(fun (id, value, t) ->
                    let* typ = typ ctx ~at t in
                    let x = Names.bind ~typ:t ctx.names id in
                    Ok
                      (R.Stmt.local ~loc:l ~const:true ~typ ~init:(R.Stmt.expr_rhs value)
                         (ident ~loc:l x)
                      @ assume_in_range ~loc:l t x)))
      in
      let last = List.last_exn bindings in
      let* ghost =
        ghost ctx ~after:last.vb_expr.exp_loc.loc_end ~before:body.exp_loc.loc_start
      in
      let* body_stmts, body = expr ~tail ctx body in
      Ok
        ( List.concat_map evaluated ~f:(fun (_, stmts, _) -> stmts)
          @ List.concat (List.concat defs)
          @ ghost @ body_stmts,
          body )
  | Texp_let (Recursive, _, _) -> unsupported at "A local recursive function"
  | Texp_sequence (e1, e2) ->
      let* stmts1, _ = expr ctx e1 in
      let* ghost = ghost ctx ~after:e1.exp_loc.loc_end ~before:e2.exp_loc.loc_start in
      let* stmts2, v = expr ~tail ctx e2 in
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
          match pure ~reads ctx ~funcs:[] [] cond with
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
  let read r field typ_of =
    let* typ = typ ctx ~at typ_of in
    let x = Names.fresh ctx.names "tmp" in
    let rhs = R.Stmt.expr_rhs (R.Expr.field ~loc:l r (name ~loc:l field)) in
    Ok
      ( R.Stmt.local ~loc:l ~typ ~init:rhs (ident ~loc:l x),
        R.Expr.var ~loc:l (name ~loc:l x) )
  in
  match (stdlib_name path, args) with
  | _ when Option.is_some (atomic_name path) ->
      atomic ctx e (Option.value_exn (atomic_name path)) args
  | Some "ref", [ v ] ->
      let* field = ref_field ctx ~at v.exp_type in
      let* stmts, v = expr ctx v in
      let x = Names.fresh ctx.names "tmp" in
      let views, view_args = view_allocation ctx ~loc:l [ field ] in
      let init = R.Stmt.new_rhs ((name ~loc:l field, Some v) :: view_args) in
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
      let* v_stmts, v = expr ctx v in
      let* r_stmts, r = expr ctx r in
      Ok (v_stmts @ r_stmts @ [ write ~loc:l r field v ], unit_value ~loc:l)
  | Some (("incr" | "decr") as op), [ r ] ->
      let* field = contents r in
      let* stmts, r = expr ctx r in
      let int_type = Predef.type_int in
      let* reading, v = read r field int_type in
      let binop : R.Expr.binop = if String.equal op "incr" then Plus else Minus in
      let v' = R.Expr.binary ~loc:l binop v (R.Expr.int ~loc:l 1) in
      let what = if String.equal op "incr" then "increment" else "decrement" in
      Ok
        ( stmts @ reading @ [ no_overflow ctx ~at what v'; write ~loc:l r field v' ],
          unit_value ~loc:l )
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
        begin match named_action ctx a.pid_str with
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
      linearize ?step ctx ~at how (R.Stmt.local ~loc:l ~typ ~init (ident ~loc:l x))
    in
    Ok (step, v)
  in
  let* elt =
    match args with
    | a :: _ when not (String.is_prefix op ~prefix:"make") -> element a.exp_type
    | _ -> element e.exp_type
  in
  let* field = atomic_field ctx ~at elt in
  let* stmts, values = operands ctx args in
  let primitive op = primitive ctx ~at elt op in
  match (op, values) with
  | ("make" | "make_contended"), [ v ] ->
      let x = Names.fresh ctx.names "tmp" in
      let views, view_args = view_allocation ctx ~loc:l [ field ] in
      let init = R.Stmt.new_rhs ((name ~loc:l field, Some v) :: view_args) in
      Ok
        ( stmts @ views
          @ R.Stmt.local ~loc:l ~typ:(R.Type.ref ~loc:l) ~init (ident ~loc:l x),
          R.Expr.var ~loc:l (name ~loc:l x) )
  | "get", [ a ] ->
      let* typ = typ ctx ~at e.exp_type in
      let x = Names.fresh ctx.names "tmp" in
      let read = R.Stmt.expr_rhs (R.Expr.field ~loc:l a (name ~loc:l field)) in
      let* how = how `Abort in
      let value = R.Expr.var ~loc:l (name ~loc:l x) in
      let* step =
        linearize ~value ctx ~at how
          (R.Stmt.local ~loc:l ~typ ~init:read (ident ~loc:l x))
      in
      record_read ctx ~atomic:a value;
      Ok (stmts @ step, R.Expr.var ~loc:l (name ~loc:l x))
  | "set", [ a; v ] ->
      let* how = how `Commit in
      let* step = linearize ctx ~at how [ write ~loc:l a field v ] in
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
        linearize ctx ~at how
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
      match path with
      | Pident id -> (
          match
            List.Assoc.find ctx.functions (Ident.unique_name id) ~equal:String.equal
          with
          | Some f -> call ctx e f args
          | None -> unsupported at "A call of a local function")
      | Pdot (Pident m, x) when List.Assoc.mem ctx.libraries m ~equal:Ident.same ->
          (* A function of a library, trusted. *)
          call ctx e
            (List.Assoc.find_exn ctx.libraries m ~equal:Ident.same ^ "." ^ x)
            args
      | _ -> unsupported at ("A call of " ^ Path.name path))
  | _ -> unsupported at "This application"

(** The call of the top-level function [f] with [args], in [e]: a statement, whose result
    is kept in a variable unless it is unit. *)
and call ctx (e : Typedtree.expression) f (ocaml_args : Typedtree.expression list) =
  let args = ocaml_args in
  let l = loc e.exp_loc in
  let* stmts_args = all (List.rev args) ~f:(fun arg -> expr ctx arg) in
  let stmts = List.concat_map stmts_args ~f:fst in
  let args = List.rev_map stmts_args ~f:snd in
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
    all
      (Option.value (List.Assoc.find ctx.ghost_args f ~equal:String.equal) ~default:[])
      ~f:(fun equation ->
        let known =
          Option.bind equation ~f:(fun (i, field) ->
              match List.nth ocaml_args (i - List.length prefix) with
              | Some { exp_desc = Texp_ident (Pident id, _, _); _ } ->
                  Option.bind (Names.find ctx.names id) ~f:(fun x ->
                      List.find_map ctx.fields_of ~f:(fun (y, (g, value)) ->
                          Option.some_if (String.equal x y && String.equal g field) value))
              | _ -> None)
        in
        match (known, equation) with
        | Some value, _ -> Ok value
        | None, None ->
            error e.exp_loc
              "Caravan cannot tell the ghost argument of this call: give the callee a \
               precondition that makes a parameter a field of it, as tail = q.tail"
        | None, Some (_, field) ->
            error e.exp_loc
              (Printf.sprintf
                 "Caravan cannot tell the ghost argument of this call: the argument is \
                  not a variable known to be the field %s of a value, as one a record \
                  pattern binds"
                 field))
  in
  let args = prefix @ args @ ghosts in
  (* A recursive call before the function linearizes is a retry, which linearizes it in
     its place, with the atomic update's values of the implicit parameters, as does a call
     of a function that continues the update. *)
  let* retry =
    match ctx.au with
    | Some au
      when String.equal au.self f
           || Option.exists role ~f:(fun r -> String.equal r au.role) ->
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
  let callee_name =
    match String.lsplit2 f ~on:'.' with
    | Some (m, x) -> R.Name.make ~loc:l ~path:[ m ] x
    | None -> name ~loc:l f
  in
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
                    (R.Name.make ~loc:l ~path:[ module_name st "state" ] "T")
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
  if is_unit e.exp_type then
    let* closing = closing (unit_value ~loc:l) in
    let call =
      match ghosts with
      | [] -> [ R.Stmt.call ~loc:l callee ]
      | _ -> ghost_decls @ [ R.Stmt.assign ~loc:l ghosts (R.Stmt.expr_rhs callee) ]
    in
    Ok (stmts @ opening @ call @ closing, unit_value ~loc:l)
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
    Ok (stmts @ opening @ def @ closing, v)

(** The statements evaluating [args], right to left as OCaml does, and their values. *)
and operands ctx (args : Typedtree.expression list) =
  let* evaluated = all (List.rev args) ~f:(fun arg -> expr ctx arg) in
  Ok (List.concat_map evaluated ~f:fst, List.rev_map evaluated ~f:snd)

(** The condition under which the value [v] matches [p], [None] if it always does, and the
    variables [p] binds, with their values and types. *)
and pattern ctx (p : Typedtree.pattern) (v : R.Expr.t) =
  let at = p.pat_loc in
  let l = loc at in
  let conjoin conds =
    List.reduce (List.filter_opt conds) ~f:(fun a b -> R.Expr.binary ~loc:l And a b)
  in
  let components ps values =
    let* matched = all (List.zip_exn ps values) ~f:(fun (p, v) -> pattern ctx p v) in
    Ok (List.map matched ~f:fst, List.concat_map matched ~f:snd)
  in
  match p.pat_desc with
  | Tpat_any -> Ok (None, [])
  | Tpat_var (id, _, _) -> Ok (None, [ (id, v, p.pat_type) ])
  | Tpat_alias (q, id, _, _, _) ->
      let* cond, binds = pattern ctx q v in
      Ok (cond, binds @ [ (id, v, p.pat_type) ])
  | Tpat_constant (Const_int n) ->
      Ok (Some (R.Expr.binary ~loc:l Eq v (R.Expr.int ~loc:l n)), [])
  | Tpat_tuple ps ->
      let values = List.mapi ps ~f:(fun i _ -> R.Expr.tuple_get ~loc:l v i) in
      let* conds, binds = components (List.map ps ~f:snd) values in
      Ok (conjoin conds, binds)
  | Tpat_record (fields, _) ->
      (* The fields of an immutable record. *)
      let* parts =
        all fields ~f:(fun (_, label, p) ->
            let* field = field_of_label ctx ~at label in
            match field with
            | Some (field, false) -> Ok (p, R.Expr.field ~loc:l v (name ~loc:l field))
            | Some (_, true) -> unsupported at "A pattern on a mutable field"
            | None -> unsupported at "This field")
      in
      let* conds, binds = components (List.map parts ~f:fst) (List.map parts ~f:snd) in
      Ok (conjoin conds, binds)
  | Tpat_construct (_, { cstr_name = ("true" | "false") as b; _ }, [], _) ->
      Ok
        (Some (R.Expr.binary ~loc:l Eq v (R.Expr.bool ~loc:l (String.equal b "true"))), [])
  | Tpat_construct (_, { cstr_name = "()"; _ }, [], _) -> Ok (None, [])
  | Tpat_construct (_, cstr, ps, _) ->
      begin match Datatypes.find_cstr ctx.types cstr with
      | None -> unsupported at "This constructor"
      | Some (_, c) ->
          let is_c = R.Expr.is_ ~loc:l v (ident ~loc:l c.raven) in
          let fields =
            List.map c.fields ~f:(fun f -> R.Expr.field ~loc:l v (name ~loc:l f))
          in
          let* conds, binds = components ps fields in
          Ok (conjoin (Some is_c :: conds), binds)
      end
  | Tpat_or (p1, p2, _) -> begin
      let* c1, b1 = pattern ctx p1 v in
      let* c2, b2 = pattern ctx p2 v in
      match (c1, c2, b1, b2) with
      | Some c1, Some c2, [], [] -> Ok (Some (R.Expr.binary ~loc:l Or c1 c2), [])
      | _, _, [], [] -> Ok (None, [])
      | _ -> unsupported at "An or-pattern binding variables"
    end
  | _ -> unsupported at "This pattern"

(** The cases of a match on the value [v], with the value of the matching one assigned to
    [target] if there is one; [total] if OCaml found them exhaustive. *)
and match_cases ?commits ~tail ctx ~at v
    (cases : (Typedtree.pattern * Typedtree.expression) list) ~total target =
  let l = loc at in
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
  let case_body binds (rhs : Typedtree.expression) =
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
          all flat ~f:(fun (case, binds, in_range, rhs) ->
              let* body = case_body binds rhs in
              Ok (case, in_range @ body))
        in
        let has_default =
          List.exists flat ~f:(fun (case, _, _, _) ->
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
              let* _, binds = pattern ctx p v in
              case_body binds rhs
          | (p, rhs) :: rest -> begin
              let* cond, binds = pattern ctx p v in
              let* body = case_body binds rhs in
              match cond with
              | None -> Ok body
              | Some cond ->
                  let* rest = chain rest in
                  Ok [ R.Stmt.if_ ~loc:l cond body rest ]
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
  let case = function
    | `Any (id, (p : Typedtree.pattern)), rhs ->
        let binds =
          Option.value_map id ~default:[] ~f:(fun id -> [ (id, v, p.pat_type) ])
        in
        (R.Expr.Default, binds, [], rhs)
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
          rhs )
  in
  Option.map (flat [] cases) ~f:(List.map ~f:case)

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
    variables in [values]; [funcs] are the functions it may call, by their OCaml
    identifiers' unique names, with their Raven names. *)
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
          Ok (R.Expr.field ~loc:l (R.Expr.var ~loc:l (name ~loc:l x)) (name ~loc:l field))
      | None -> not_pure "This field"
    end
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
      | None, None, Pident id, _ ->
          begin match
            List.Assoc.find funcs (Ident.unique_name id) ~equal:String.equal
          with
          | Some f -> Ok (R.Expr.call ~loc:l (name ~loc:l f) args)
          | None -> not_pure ("A call of " ^ Ident.name id)
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
            all flat ~f:(fun (case, binds, _, rhs) ->
                let* body = pure_in (with_binds binds) rhs in
                Ok (case, body))
          in
          Ok (R.Expr.match_ ~loc:l v cases)
      | None ->
          (* OCaml found the cases exhaustive, so the last one needs no test. *)
          let rec chain = function
            | [] -> not_pure "An empty match"
            | [ (p, rhs) ] ->
                let* _, binds = pattern ctx p v in
                pure_in (with_binds binds) rhs
            | (p, rhs) :: rest -> begin
                let* cond, binds = pattern ctx p v in
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
  raven_name : string;
  params : Typedtree.function_param list;
  body : Typedtree.expression;
  loc : Location.t;
  contract : S.contract option;
  next : Location.t option;  (** The location of the next structure item, if any. *)
  prefix : Ident.t list;
      (** The variables of the parameters of the function that a lifted local function
          continues, which its parameters start with. *)
  prefix_count : int;  (** The number of those parameters. *)
  captured : Ident.t list;
      (** The variables of its context that a lifted local function uses, which it takes
          next. *)
  trusted : bool;
      (** Whether the function is trusted, as [(*@ trusted *)] after it says: its contract
          assumed, its body not translated. *)
  role : string option;  (** The function whose atomic update it continues. *)
}
(** A top-level function [f] with its parameters [params] and [body], and its contract, or
    a local function lifted to the top level. *)

(** The ghost parameters that the contract of [f] gives it, as [q] in
    [fix_tail [q : t] tail new_tail]. *)
let ghost_params (f : func) =
  match Option.bind f.contract ~f:(fun c -> c.header) with
  | Some h ->
      List.filter_map h.hd_args ~f:(function
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
      let* result =
        match h.hd_ret with
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
            let* cond, binds = pattern ctx pat value in
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
                Ok stmts
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
      vars = List.map named ~f:(fun (x, r, _) -> (x, Raven r));
    }
  in
  (* Ghost parameters, as [q] in [fix_tail [q : t] tail new_tail]. *)
  let* ghosts =
    all (ghost_params f) ~f:(fun (id, pty) ->
        let* t = Source.ocaml_type ctx.env ~at:id.pid_loc pty in
        Ok (id.pid_str, Names.fresh ctx.names id.pid_str, t))
  in
  let env =
    List.fold ghosts ~init:env ~f:(fun env (x, raven, t) ->
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
    [c] in [requires node = Next (v, c)]: the value's fields. *)
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
    | ( { term_desc = Tvar (Qid { pid_str = "="; _ }); _ },
        [ ({ term_desc = Tvar (Qid { pid_str = x; _ }); _ } as value); rhs ] )
      when List.Assoc.mem env.vars x ~equal:String.equal ->
        begin match spine rhs [] with
        | { term_desc = Tvar (Qid { pid_str = c; _ }); _ }, args
          when Char.is_uppercase c.[0] -> begin
            let args =
              match args with [ { term_desc = Ttuple ts; _ } ] -> ts | _ -> args
            in
            match (Datatypes.find_ctor env.data c, formula env value) with
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
                             (Value (R.Expr.field ~loc:l v (R.Name.make ~loc:l field))))
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

(** The function that contracts call for [f], defined by its body; [funcs] are the
    functions it may call, by their OCaml identifiers' unique names, and [spec_funcs] by
    their OCaml names. Its postconditions are those of [f], under the preconditions that
    do not call [f] itself: these are proven for the function's value, by induction, which
    a precondition bounding the function's own value, as for the code to not overflow,
    would make circular. *)
let func types ~refs ~primitives ~shared ~ocaml_env ~preds ~funcs ~spec_funcs
    ~proof_support origins (f : func) : (R.Callable.t, error) Result.t =
  let ctx =
    {
      types;
      refs;
      primitives;
      names = Names.create ();
      functions = [];
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
      linearizations = [];
      shared;
      invariants = [];
      opened = [];
      snapshots = [];
      positions = [];
      formals = [];
      ghost_args = [];
      fields_of = [];
      libraries = [];
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
  let calls_self (t : S.term) =
    List.mem (term_names t) (Ident.name f.id) ~equal:String.equal
  in
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
       ~ensures (ident ~loc:l f.raven_name) (Some body))

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
  | Tvar (Qid { pid_str = p; _ }), _, _
    when List.Assoc.mem ctx.preds p ~equal:String.equal ->
      let raven, types = List.Assoc.find_exn ctx.preds p ~equal:String.equal in
      let* args =
        if List.length types = List.length args then
          all (List.zip_exn types args) ~f:(fun (t, a) -> expected_formula env (Some t) a)
        else all args ~f:(formula env)
      in
      Ok (make ~loc:l ~pred:p (name ~loc:l raven) args)
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
let invariant_apps ctx env (terms : S.term list) =
  let rec apps (t : S.term) =
    let t = S.chain t in
    match spine t [] with
    | { term_desc = Tvar (Qid { pid_str = "&&" | "/\\"; _ }); _ }, [ a; b ] ->
        apps a @ apps b
    | { term_desc = Tvar (Qid { pid_str = p; _ }); _ }, args
      when List.Assoc.mem ctx.shared.persistent p ~equal:String.equal ->
        [ (p, args) ]
    | _ -> []
  in
  all (List.concat_map terms ~f:apps) ~f:(fun (p, args) ->
      let raven, _ = List.Assoc.find_exn ctx.preds p ~equal:String.equal in
      let* args = all args ~f:(formula env) in
      Ok (raven, args))

(** The statements establishing the invariant [inv] with [args] at the end of [f], at
    [at]: with the initial state of its structure, as [f]'s annotation
    [(*@ initially { ... } *)] gives it, the history of that state and the index maps of
    its fields owned by index. *)
let establish_invariant ctx ~(f : func) ~at inv args =
  let l = loc at in
  match List.find ctx.shared.structures ~f:(fun st -> String.equal st.invariant inv) with
  | None -> Ok [ R.Stmt.fold ~loc:l (name ~loc:l inv) args ]
  | Some st -> begin
      let window (a : Annotation.t) =
        a.loc.loc_start.pos_cnum >= f.body.exp_loc.loc_end.pos_cnum
        && Option.for_all f.next ~f:(fun next ->
            a.loc.loc_end.pos_cnum <= next.loc_start.pos_cnum)
        && Poly.equal (Annotation.kind a) Annotation.Initially
      in
      match List.filter ctx.annotations ~f:window with
      | [] when (not (has_history st)) && List.is_empty st.chains ->
          (* The witnesses are computed. *)
          Ok [ R.Stmt.fold ~loc:l (name ~loc:l inv) args ]
      | [] ->
          error f.loc
            (Printf.sprintf
               "This function establishes %s, whose initial state it gives as (*@ \
                initially { ... } *)"
               inv)
      | a :: _ ->
          let* initial = Annotation.initially a in
          let env = scope_env ctx in
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
          let* indices =
            all st.chains ~f:(fun (field, index) ->
                let _, _, term =
                  List.find_exn values ~f:(fun (raven, _, _) ->
                      String.equal raven (st.state ^ "_" ^ field))
                in
                match entries term with
                | Some es ->
                    let* es = all es ~f:(formula env) in
                    Ok
                      ( ident ~loc:l index,
                        R.Expr.map_literal ~loc:l
                          (List.mapi es ~f:(fun i e -> (e, R.Expr.int ~loc:l i)))
                          (R.Expr.int ~loc:l 0) )
                | None ->
                    unsupported term.term_loc
                      "An initial value other than a list of entries, for a field owned \
                       by index,")
          in
          (* The keys of no registrations. *)
          let ons =
            List.map st.pendings ~f:(fun p ->
                ( ident ~loc:l p.pending_on,
                  R.Expr.map_literal ~loc:l [] (R.Expr.null ~loc:l) ))
          in
          let history =
            if has_history st then
              let qn m x = R.Name.make ~loc:l ~path:[ m ] x in
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
                      (name ~loc:l (member_name st "history"))
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
                            (name ~loc:l (member_name st "states"))
                            [ state ]);
                     ]);
              ]
            else []
          in
          Ok
            (history
            @ [
                R.Stmt.fold ~loc:l
                  ~witnesses:
                    (List.map values ~f:(fun (raven, v, _) -> (ident ~loc:l raven, v))
                    @ indices @ ons)
                  (name ~loc:l inv) args;
              ])
    end

(** The procedure of [f], named [proc_name]; if [f] is pure, its result is the value of
    its function. [funcs] are the functions contracts can call, by their OCaml names. *)
let proc types ~refs ~primitives ~shared ~ocaml_env ~preds ~funcs ~annotations
    ~linearizations ~lifted ~pasts ~past_returns ~ghost_args ~libraries ~proof_lemmas
    ~proof_support (functions : (string * string) list) origins ~proc_name ~pure
    (f : func) : (R.Callable.t, error) Result.t =
  let names = Names.create () in
  let ctx =
    {
      types;
      refs;
      primitives;
      names;
      functions;
      lifted;
      pasts;
      past_returns;
      ghost_args;
      libraries;
      origins;
      annotations;
      spec_funcs = funcs;
      proof_lemmas;
      proof_support;
      predicate_bodies = [];
      env = ocaml_env;
      preds;
      facts = [];
      au = None;
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
        match past_of shared.structures t with Some p -> First p | None -> Second t)
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
  (* Ghost statements and invariants in the code can use the implicit parameters. *)
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
  ctx.invariants <- invariants;
  (* A snapshot and a position witnessing each fact about an earlier state. *)
  let witnesses (p : past) =
    let* st =
      match
        List.find shared.structures ~f:(fun st -> String.equal st.invariant p.inv)
      with
      | Some st -> Ok st
      | None -> error p.element.term_loc "A fact about an earlier state without a state"
    in
    let* structure =
      match List.Assoc.find invariants p.inv ~equal:String.equal with
      | Some (x :: _) ->
          let anchored =
            match anchor types st.structure_type with
            | Some (_, at) -> at ~loc:l x
            | None -> x
          in
          Ok (R.Expr.field ~loc:l anchored (name ~loc:l (member_name st "history")))
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
                 (R.Name.make ~loc:l ~path:[ module_name st "state" ] "T")
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
  let postconditions ?atomic posts =
    let* free = free_typed env posts ~at:f.loc in
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
          List.map free ~f:(fun (_, raven, _, typ, l) ->
              R.Var.make ~loc:l (ident ~loc:l raven) typ)
        in
        Ok [ R.Spec.make ?atomic (R.Expr.exists ~loc:l vars conj) ]
  in
  let* ensures =
    postconditions (Option.value_map f.contract ~default:[] ~f:(fun c -> c.ensures))
  in
  let atomic_posts =
    Option.value_map f.contract ~default:[] ~f:(fun c -> c.atomic_ensures)
  in
  let* atomic_ensures = postconditions ~atomic:true atomic_posts in
  let* bind_au =
    if atomic then
      atomic_update ctx env ~at:f.loc ~self:proc_name
        ~role:(Option.value f.role ~default:(Ident.name f.id))
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
    if pure && not (List.is_empty returns) then
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
             (R.Expr.call ~loc:l (name ~loc:l f.raven_name) args));
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
      (R.Callable.proc ~loc:l ~formals:all_formals ~returns:(returns @ past_returns)
         ~requires ~ensures (ident ~loc:l proc_name) None)
  end
  else
    let* first = ghost ctx ~after:f.loc.loc_start ~before:f.body.exp_loc.loc_start in
    let* stmts, v = expr ~tail:true ctx f.body in
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
        let* views = all posts ~f:(uses ctx env ~at:f.loc (with_views ctx only_views)) in
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
        let* folds =
          all established ~f:(fun (inv, args) -> establish_invariant ctx ~f ~at inv args)
        in
        Ok (List.concat views @ List.concat folds)
    in
    let body = bind_au @ bound @ first @ stmts @ assignment @ establish @ last in
    Ok
      (R.Callable.proc ~loc:l ~formals:all_formals ~returns:(returns @ past_returns)
         ~requires ~ensures (ident ~loc:l proc_name) (Some body))

(** The entry [element] of a fact that [f] ensures about an earlier state, given the
    arguments of a call: a parameter, which [names] names, or the argument of a
    constructor that a precondition matches a parameter with, as [c] in
    [requires node = Next (v, c)]. *)
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
        | ( { term_desc = Tvar (Qid { pid_str = "="; _ }); _ },
            [ { term_desc = Tvar (Qid { pid_str = x; _ }); _ }; rhs ] ) ->
            begin match (param x, spine rhs []) with
            | Some i, ({ term_desc = Tvar (Qid { pid_str = c; _ }); _ }, args) -> begin
                let args =
                  match args with [ { term_desc = Ttuple ts; _ } ] -> ts | _ -> args
                in
                match Datatypes.find_ctor types c with
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
                R.Expr.field ~loc:l a (R.Name.make ~loc:l field))
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
            role = Some (Ident.name g.id);
          }
      | _ -> f)

(** The parameters and body of the function [e]: as written, or, for
    [function p1 -> e1 | ...], with its last parameter and a match on it. *)
let function_parts (e : Typedtree.expression) =
  match e.exp_desc with
  | Texp_function (params, Tfunction_body body) -> Some (params, body)
  | Texp_function (params, Tfunction_cases { cases; partial; param; loc; _ }) -> begin
      (* The type of the last parameter, and the result's, after the others. *)
      let rec after n (t : Types.type_expr) =
        match Types.get_desc t with
        | Tarrow (_, a, r, _) -> if n = 0 then Some (a, r) else after (n - 1) r
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
let contract_after (annotations : Annotation.t list) ~(item_loc : Location.t)
    ~(next : Location.t option) : (S.contract option, error) Result.t =
  let after (a : Annotation.t) =
    a.loc.loc_start.pos_cnum >= item_loc.loc_end.pos_cnum
    && Option.for_all next ~f:(fun next ->
        a.loc.loc_end.pos_cnum <= next.loc_start.pos_cnum)
  in
  match
    List.filter annotations ~f:(fun a ->
        after a && Poly.equal (Annotation.kind a) Annotation.Contract)
  with
  | [] -> Ok None
  | [ a ] -> Result.map (Annotation.contract a) ~f:Option.some
  | _ :: a :: _ -> error a.loc "A function has at most one contract"

(** Whether [(*@ trusted *)] annotates the item at [item_loc], ending before [next]. *)
let trusted_after (annotations : Annotation.t list) ~(item_loc : Location.t)
    ~(next : Location.t option) =
  List.exists annotations ~f:(fun a ->
      a.loc.loc_start.pos_cnum >= item_loc.loc_end.pos_cnum
      && Option.for_all next ~f:(fun next ->
          a.loc.loc_end.pos_cnum <= next.loc_start.pos_cnum)
      && Poly.equal (Annotation.kind a) Annotation.Trusted)

(** The contracts of the values of [interface], by their names: an annotation after the
    value's declaration. *)
let interface_contracts (interface : Source.interface) =
  let annotations = Annotation.of_comments interface.interface_comments in
  let items = interface.signature in
  let nexts =
    List.map (List.drop items 1) ~f:(fun (i : Parsetree.signature_item) ->
        Some i.psig_loc)
    @ [ None ]
  in
  let* contracts =
    all (List.zip_exn items nexts) ~f:(fun ((item : Parsetree.signature_item), next) ->
        match item.psig_desc with
        | Psig_value vd ->
            let* contract = contract_after annotations ~item_loc:item.psig_loc ~next in
            Ok (Option.map contract ~f:(fun c -> (vd.pval_name.txt, (c, item.psig_loc))))
        | _ -> Ok None)
  in
  Ok (List.filter_opt contracts)

(** The data types and functions of [structure], in order, with the contracts of the
    functions in [annotations], or in [interface], by their names. *)
let items ?(interface = []) (structure : Typedtree.structure)
    (annotations : Annotation.t list) : (Datatypes.t list * func list, error) Result.t =
  let items = structure.str_items in
  let nexts =
    List.map (List.drop items 1) ~f:(fun (i : Typedtree.structure_item) -> Some i.str_loc)
    @ [ None ]
  in
  (* A definition that a later one of the same name shadows is named apart, and the
     interface's contract is the last one's. *)
  let defined =
    List.concat_map items ~f:(fun (i : Typedtree.structure_item) ->
        match i.str_desc with
        | Tstr_value (_, bindings) ->
            List.filter_map bindings ~f:(fun (vb : Typedtree.value_binding) ->
                match vb.vb_pat.pat_desc with Tpat_var (id, _, _) -> Some id | _ -> None)
        | _ -> [])
  in
  let shadowed id =
    let rec after = function
      | [] -> []
      | x :: rest -> if Ident.same x id then rest else after rest
    in
    List.exists (after defined) ~f:(fun x -> String.equal (Ident.name x) (Ident.name id))
  in
  let earlier id =
    List.count
      (List.take_while defined ~f:(fun x -> not (Ident.same x id)))
      ~f:(fun x -> String.equal (Ident.name x) (Ident.name id))
  in
  let item ((item : Typedtree.structure_item), next) =
    match item.str_desc with
    | Tstr_type (_, decls) ->
        let* types = all decls ~f:Datatypes.of_declaration in
        Ok (types, [])
    | Tstr_value (_, bindings) ->
        let* funcs =
          all bindings ~f:(fun (vb : Typedtree.value_binding) ->
              match (vb.vb_pat.pat_desc, function_parts vb.vb_expr) with
              | Tpat_var (id, _, _), Some (params, body) ->
                  let* contract =
                    contract_after annotations ~item_loc:item.str_loc ~next
                  in
                  let* contract =
                    match
                      ( contract,
                        if shadowed id then None
                        else List.Assoc.find interface (Ident.name id) ~equal:String.equal
                      )
                    with
                    | Some _, Some (_, at) ->
                        error vb.vb_loc
                          ~related:[ (at, "Its contract in the interface") ]
                          (Printf.sprintf
                             "%s has a contract in its interface and another one here"
                             (Ident.name id))
                    | Some c, None | None, Some (c, _) -> Ok (Some c)
                    | None, None -> Ok None
                  in
                  Ok
                    {
                      id;
                      raven_name =
                        (if shadowed id then
                           Printf.sprintf "%s_%d" (Ident.name id) (earlier id + 1)
                         else Ident.name id);
                      params;
                      body;
                      loc = vb.vb_loc;
                      contract;
                      next;
                      prefix = [];
                      prefix_count = 0;
                      captured = [];
                      role = None;
                      trusted = trusted_after annotations ~item_loc:item.str_loc ~next;
                    }
              | _ -> unsupported vb.vb_loc "This definition")
        in
        Ok ([], funcs)
    | _ -> unsupported item.str_loc "This structure item"
  in
  let* items = all (List.zip_exn items nexts) ~f:item in
  Ok (List.concat_map items ~f:fst, List.concat_map items ~f:snd)

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
let local_functions (outer : func) (annotations : Annotation.t list) =
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
          raven_name = Ident.name id;
          params = prefix_params @ captured_params @ params;
          body;
          loc = vb.vb_loc;
          contract;
          next = Some rest.exp_loc;
          prefix;
          prefix_count = List.length prefix_params;
          captured;
          trusted =
            trusted_after annotations ~item_loc:vb.vb_loc ~next:(Some rest.exp_loc);
          role = Option.map continues ~f:(fun g -> g.pid_str);
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

(** The functions of [funcs] that must be pure: those that contracts call or say are
    [pure], and the functions these call. *)
let pure_functions (funcs : func list) : func list =
  let contract_names =
    List.concat_map funcs ~f:(fun f ->
        Option.value_map f.contract ~default:[] ~f:(fun (c : S.contract) ->
            List.concat_map (c.requires @ c.ensures @ c.variant) ~f:term_names))
  in
  let seeds =
    List.filter funcs ~f:(fun f ->
        List.mem contract_names (Ident.name f.id) ~equal:String.equal
        || Option.exists f.contract ~f:(fun (c : S.contract) -> c.pure))
  in
  let is_in set (f : func) = List.exists set ~f:(fun g -> Ident.same g.id f.id) in
  let rec close set =
    let called = List.concat_map set ~f:(fun f -> referenced f.body) in
    let added =
      List.filter funcs ~f:(fun f ->
          (not (is_in set f)) && List.exists called ~f:(fun id -> Ident.same id f.id))
    in
    if List.is_empty added then set else close (set @ added)
  in
  close seeds

(** How a predicate is defined: by a body; as an invariant, by a body in terms of the
    fields of its state; or as a view of an invariant's state. *)
type definition =
  | Body of S.term
  | Invariant of { state : string; fields : S.state_field list; body : S.term }
  | View of { value : S.term }

(** The ghost field holding the client's view [v] of a state. *)
let view_field v = "view_" ^ v

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
  let qn m x = R.Name.make ~loc:l ~path:[ m ] x in
  let var x = R.Expr.var ~loc:l (n x) in
  let call f args = R.Expr.call ~loc:l f args in
  let bin op a b = R.Expr.binary ~loc:l op a b in
  let state_module = module_name st "state" in
  let state_type = R.Type.named ~loc:l (qn state_module "T") [] in
  let decl x t = R.Var.make ~loc:l (ident ~loc:l x) t in
  let length s = call (qn "Seq" "length") [ s ] in
  let extends a b = call (n (member_name st "extends")) [ a; b ] in
  let states s = call (n (member_name st "states")) [ s ] in
  let set_module = module_name st "states"
  and history_module = module_name st "history" in
  let auth s = call (qn history_module "auth") [ call (qn set_module "set") [ s ] ] in
  let history_field = member_name st "history" in
  let* structure_typ = Datatypes.typ types ~at st.structure_type in
  let* anchored =
    match anchor types st.structure_type with
    | Some (_, at) -> Ok (fun e -> R.Expr.field ~loc:l (at ~loc:l e) (n history_field))
    | None ->
        error at "The structure of a state is a reference: an atomic, a ref or a record"
  in
  let state_data =
    R.Member.module_ ~loc:l (ident ~loc:l state_module)
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
         (ident ~loc:l name) (Some body))
  in
  let lemma ?auto ?triggers name formals ~requires ~ensures body =
    R.Member.callable
      (R.Callable.proc ~loc:l ~kind:Lemma ?auto ~formals
         ~requires:(List.map requires ~f:R.Spec.make)
         ~ensures:(List.map ensures ~f:(R.Spec.make ?triggers))
         (ident ~loc:l name) (Some body))
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
         (ident ~loc:l set_module)
         (R.Name.make ~loc:l ~path:[ "Library" ] "SetRA");
       R.Member.instance ~loc:l
         ~def:
           ( R.Name.make ~loc:l ~path:[ "Library" ] "Auth",
             [ R.Type.named ~loc:l (n set_module) [] ] )
         (ident ~loc:l history_module)
         (R.Name.make ~loc:l ~path:[ "Library" ] "Auth");
       R.Member.field ~loc:l ~ghost:true (ident ~loc:l history_field)
         (R.Type.named ~loc:l (n history_module) []);
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
      | { term_desc = Tvar (Qid { pid_str = v; _ }); _ }, args ->
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
  | { term_desc = Tvar (Qid { pid_str = p; _ }); _ }, _
    when List.Assoc.mem ctx.preds p ~equal:String.equal || String.equal p "own" ->
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
  let field e f = R.Expr.field ~loc:l e (n (pending_name st p f)) in
  let half e f v = R.Expr.own ~loc:l [ field e f; v; R.Expr.real ~loc:l 0.5 ] in
  let decl ?(ghost = false) x t = R.Var.make ~loc:l ~ghost (ident ~loc:l x) t in
  let* key_typ = typ ctx ~at p.key_type in
  let token_typ = R.Type.atomic_token ~loc:l (n helped_proc) in
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
  let registered hc = R.Expr.call ~loc:l (n registration) (hc :: args) in
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
        R.Member.field ~loc:l ~ghost:true (ident ~loc:l (pending_name st p f)) t)
  in
  (* The registration of a call: its update until it retires, committed once helped. *)
  let hc = var "hc" in
  let registration_pred =
    R.Callable.func ~loc:l ~kind:Pred
      ~formals:(decl "hc" ref_typ :: List.map params ~f:(fun (_, _, d) -> d))
      (ident ~loc:l registration)
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
                      (R.Expr.au_commit ~loc:l (n helped_proc)
                         ((var "tok" :: args) @ [ result ]))
                      (R.Expr.au ~loc:l (n helped_proc) (var "tok" :: args)));
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
        let view_field = List.Assoc.find_exn ctx.shared.views v ~equal:String.equal in
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
            R.Expr.field ~loc:l (anchored structure) (n view_field);
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
  let post_env = bind post_env result_name (Value result) in
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
  let call f es = R.Stmt.call ~loc:l (R.Expr.call ~loc:l (n f) es) in
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
        use ~loc:l (n raven) (args @ [ var (x ^ "_1") ]))
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
                    (n registration) (hc :: args);
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
                    (n registration) (hc :: args);
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
      ~decreases:[ regs ] (ident ~loc:l help) (Some body)
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

(** The declaration of the value [name] of a library, of a function type with the
    parameter types [args] and the result type [result], or of the type [result]: a
    procedure with [contract] if it has one, or a function without arguments. Names free
    in the preconditions are implicit ghost parameters, those free in the postconditions
    are existentially quantified. *)
let library_function ctx ~(at : Location.t) ~name ~args ~result
    (contract : S.contract option) =
  let l = loc at in
  let x = ident ~loc:l name in
  let* result_typ = typ ctx ~at result in
  match (args, contract) with
  | [], None ->
      Ok
        (R.Callable.func ~loc:l
           ~returns:[ R.Var.make ~loc:l (ident ~loc:l "r") result_typ ]
           x None)
  | [], Some _ -> unsupported at "A contract of a library's value other than a function"
  | _, Some { atomic = true; _ } ->
      unsupported at "An atomic contract of a library's function"
  | _ ->
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
                (Printf.sprintf "This contract names %d arguments, but %s has %d"
                   (List.length names) name (List.length args))
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
      let requires = Option.value_map contract ~default:[] ~f:(fun c -> c.requires) in
      let ensures = Option.value_map contract ~default:[] ~f:(fun c -> c.ensures) in
      let* implicit = free_typed env requires ~at in
      let env =
        List.fold implicit ~init:env ~f:(fun env (n, raven, t, _, _) ->
            { (bind env n (Raven raven)) with var_types = (n, t) :: env.var_types })
      in
      let* requires = all requires ~f:(formula env) in
      let* existentials = free_typed env ensures ~at in
      let post_env =
        List.fold existentials ~init:env ~f:(fun env (n, raven, t, _, _) ->
            { (bind env n (Raven raven)) with var_types = (n, t) :: env.var_types })
      in
      let* ensures = all ensures ~f:(formula post_env) in
      let ensures =
        match (existentials, ensures) with
        | [], _ | _, [] -> ensures
        | _ ->
            [
              R.Expr.exists ~loc:l
                (List.map existentials ~f:(fun (_, raven, _, typ, _) ->
                     R.Var.make ~loc:l (ident ~loc:l raven) typ))
                (List.reduce_exn ensures ~f:(fun a b -> R.Expr.binary ~loc:l And a b));
            ]
      in
      Ok
        (R.Callable.proc ~loc:l
           ~formals:
             (List.map params ~f:(fun (_, _, _, v) -> v)
             @ List.map implicit ~f:(fun (_, raven, _, typ, _) ->
                 R.Var.make ~loc:l ~ghost:true ~implicit:true (ident ~loc:l raven) typ))
           ~returns
           ~requires:(List.map requires ~f:R.Spec.make)
           ~ensures:(List.map ensures ~f:R.Spec.make)
           x None)

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
              match Datatypes.find_ctor ctx.types c with
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
                              (name ~loc:l (member_name st "extends"))
                              [ state opened.values; state (List.map next ~f:fst) ]);
                       ]
                     (ident ~loc:l (member_name st (a.action ^ "_grows")))
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
    names = Names.create ();
    functions = [];
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
    linearizations = [];
    shared;
    invariants = [];
    opened = [];
    snapshots = [];
    positions = [];
    formals = [];
    ghost_args = [];
    fields_of = [];
    libraries = [];
  }

(** Recursive proof calls need checked well-founded descent, including mutual calls. *)
let check_lemma_recursion declarations =
  let rec calls bound (body : S.proof_expr) =
    match body.proof_desc with
    | Proof_value t ->
        let head, _ = spine t [] in
        begin match head.term_desc with
        | Tvar (Qid id) when not (List.mem bound id.pid_str ~equal:String.equal) ->
            [ id.pid_str ]
        | _ -> []
        end
    | Proof_let (pattern, rhs, body) ->
        calls bound rhs @ calls (pat_names pattern @ bound) body
    | Proof_seq (rhs, body) -> calls bound rhs @ calls bound body
    | Proof_if (_, yes, no) -> calls bound yes @ calls bound no
    | Proof_match (_, cases) ->
        List.concat_map cases ~f:(fun (pattern, body) ->
            calls (pat_names pattern @ bound) body)
    | Proof_fold _ | Proof_unfold _ | Proof_assert _ -> []
  in
  let graph =
    List.filter_map declarations ~f:(function
      | S.Proof_lemma { lemma_name; lemma_params; lemma_body; _ } ->
          Some
            ( lemma_name.pid_str,
              calls (List.map lemma_params ~f:(fun (id, _) -> id.S.pid_str)) lemma_body )
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
    ~proof_lemmas ~proof_support ~predicate_bodies origins declaration =
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
      let declare (id, _) ty =
        let* raven_type = typ ctx ~at:id.S.pid_loc ty in
        let raven = Names.fresh ctx.names id.pid_str in
        Ok
          ( id.pid_str,
            raven,
            ty,
            R.Var.make ~loc:(loc id.pid_loc) ~ghost:true (ident ~loc:l raven) raven_type
          )
      in
      let* inputs =
        all (List.zip_exn lemma_params signature.lemma_inputs) ~f:(fun (parameter, ty) ->
            declare parameter ty)
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
           (ident ~loc:l signature.lemma_raven)
           (Some body))
  | _ -> error Location.none "Expected a lemma declaration"

(** The predicate [p], declared at [at], whose parameters have the OCaml types
    [param_types], defined as [def]; [views] are the views of the program, for an
    invariant to hold its half of each. *)
let predicate types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs ~proof_support
    origins ~at ~views ~structures (p : S.predicate) (def : definition) param_types :
    (R.Callable.t, error) Result.t =
  let ctx =
    spec_context types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
      ~proof_support origins
  in
  let l = loc at in
  let* params, env = pred_params ctx ~at p param_types in
  let vars = List.map ~f:(fun (_, _, _, v) -> v) in
  let name = ident ~loc:l p.pred_name.pid_str in
  match def with
  | Body body ->
      let* body = quantified env body in
      (* The trailing parameters without references, as the abstract value, are outputs:
         determined by the others, which Raven checks, and found by Raven at calls. *)
      let inputs, outputs =
        let n =
          List.length
            (List.take_while (List.rev params) ~f:(fun (_, _, t, _) ->
                 not (Datatypes.has_refs types t)))
        in
        let n = if n = List.length params then 0 else n in
        List.split_n params (List.length params - n)
      in
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
          (R.Name.make ~loc:l (view_field p.pred_name.pid_str))
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
  | Invariant { state; fields = _; body } ->
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
                  [ R.Expr.field ~loc:l (var c) (R.Name.make ~loc:l field); value ]))
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
              R.Expr.field ~loc:l hc (R.Name.make ~loc:l (pending_name st p f))
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
                (R.Name.make ~loc:l (pending_name st p "registration"))
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
                (R.Name.make ~loc:l (view_field v.pred_name.pid_str))
            in
            Ok (R.Expr.own ~loc:l [ field; value; R.Expr.real ~loc:l 0.5 ]))
      in
      let history =
        if has_history st then
          let qn m x = R.Name.make ~loc:l ~path:[ m ] x in
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
                  (R.Name.make ~loc:l (member_name st "history"));
                R.Expr.call ~loc:l
                  (qn (module_name st "history") "auth")
                  [
                    R.Expr.call ~loc:l
                      (qn (module_name st "states") "set")
                      [
                        R.Expr.call ~loc:l
                          (R.Name.make ~loc:l (member_name st "states"))
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
let predicates (source : Source.t) =
  let of_annotations comments =
    all
      (List.filter (Annotation.of_comments comments) ~f:(fun a ->
           Poly.equal (Annotation.kind a) Annotation.Predicate))
      ~f:(fun a ->
        let* p = Annotation.predicate a in
        Ok (a.loc, p))
  in
  let* declared =
    Option.value_map source.interface ~default:(Ok []) ~f:(fun i ->
        of_annotations i.interface_comments)
  in
  let* annotated = of_annotations source.comments in
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
      | Proof_state _ | Proof_action _ | Proof_lemma _ | Proof_type _ | Proof_resource _
      | Proof_field _ | Proof_function _ ->
          Ok None
      | Proof_invariant { inv_name; inv_params; inv_state = state, state_type; inv_body }
        ->
          let* fields =
            match state_type with
            | PTtyapp (Qid t, []) when List.Assoc.mem states t.pid_str ~equal:String.equal
              ->
                Ok (List.Assoc.find_exn states t.pid_str ~equal:String.equal)
            | _ ->
                error state.pid_loc
                  "The state of an invariant has a type declared in the proof, as type \
                   state = { ... }"
          in
          Ok
            (Some
               ( inv_name.pid_loc,
                 {
                   S.pred_name = inv_name;
                   pred_params = inv_params;
                   pred_body = None;
                   pred_persistent = true;
                 },
                 Some (Invariant { state = state.pid_str; fields; body = inv_body }) ))
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
  let is_invariant = function Invariant _ -> true | Body _ | View _ -> false in
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
             Printf.sprintf
               "The predicate %s is declared [@persistent], so it is defined as an \
                invariant"
               (name p)
           else
             Printf.sprintf "The invariant %s is declared without [@persistent]" (name p))
    | None, _ -> Ok ()
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
let rec pure_logical_body preds (t : S.term) =
  let visit = pure_logical_body preds in
  match t.term_desc with
  | Tvar q
    when String.equal (qualid_key q) "own"
         || List.Assoc.mem preds (qualid_key q) ~equal:String.equal ->
      error t.term_loc "A pure logical function cannot use ownership or predicates"
  | Tapply (a, b) | Tinfix (a, _, b) | Tlet (_, a, b) ->
      let* () = visit a in
      visit b
  | Tif (a, b, c) ->
      let* () = visit a in
      let* () = visit b in
      visit c
  | Tmatch (value, cases) ->
      let* () = visit value in
      Result.all_unit (List.map cases ~f:(fun (_, body) -> visit body))
  | Tquant (_, _, body)
  | Tcomprehension (_, body)
  | Tfield (body, _)
  | Tattr (_, body)
  | Tcast (body, _)
  | Told body ->
      visit body
  | Ttuple ts -> Result.all_unit (List.map ts ~f:visit)
  | Ttrue | Tfalse | Tconst _ | Tvar _ -> Ok ()

(** Nonrecursive logical definitions are checked with the rest of the proof. *)
let proof_function types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
    ~proof_support origins declaration =
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
      let* () = pure_logical_body preds function_body in
      let* () =
        Source.check_logical_function ocaml_env ~functions:(List.map spec_funcs ~f:fst)
          declaration
      in
      let* body = formula env function_body in
      let result = Names.fresh ctx.names "result" in
      Ok
        (R.Callable.func ~loc:l
           ~formals:(List.map params ~f:(fun (_, _, _, v) -> v))
           ~returns:[ R.Var.make ~loc:l (ident ~loc:l result) result_type ]
           (ident ~loc:l function_name.pid_str)
           (Some (R.Expr.annotated body result_type)))
  | _ -> error Location.none "Expected a logical function declaration"

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
  let* () =
    match
      List.find linearizations ~f:(fun (anchor, _) ->
          not (List.mem steps anchor ~equal:Int.equal))
    with
    | Some (_, a) ->
        error a.loc "This annotation does not follow an atomic step, as Atomic.get t"
    | None -> Ok ()
  in
  let* interface =
    Option.value_map source.interface ~default:(Ok []) ~f:interface_contracts
  in
  let* types, funcs = items ~interface typed annotations in
  let* lifted = all funcs ~f:(fun f -> local_functions f annotations) in
  let funcs = inherit_contracts (funcs @ List.concat lifted) in
  (* The abstract types of the libraries. *)
  let* library_types =
    all source.libraries ~f:(fun (lib : Source.library) ->
        all lib.library.signature ~f:(fun (item : Parsetree.signature_item) ->
            match item.psig_desc with
            | Psig_type (_, decls) ->
                all decls ~f:(fun (decl : Parsetree.type_declaration) ->
                    match (decl.ptype_kind, decl.ptype_manifest, decl.ptype_params) with
                    | Ptype_abstract, None, [] ->
                        Ok
                          (Datatypes.library_type ~library:lib.library_name
                             ~library_id:lib.library_id ~at:decl.ptype_loc
                             decl.ptype_name.txt)
                    | _ ->
                        unsupported decl.ptype_loc
                          "A type of a library other than an abstract one without \
                           parameters")
            | _ -> Ok []))
  in
  let types = List.concat (List.concat library_types) @ types @ source.proof_types in
  (* The data types, and the sequences of specifications, which have no module. *)
  let data_types = types in
  let resource_types =
    List.concat_map source.proof_resources ~f:(fun r ->
        r.Source.resource_descriptor :: r.resource_aliases)
  in
  let types =
    types @ resource_types @ source.logical_types
    @ match source.sequence with Pident id -> [ Datatypes.sequence id ] | _ -> []
  in
  (* Each data type's module, given the ones declared before it; a record type that is a
     reference has fields instead. *)
  let* modules =
    all
      (List.filter_mapi data_types ~f:(fun i (d : Datatypes.t) ->
           Option.some_if
             (Option.is_none d.heap && Option.is_none d.alias)
             (List.take data_types i, d)))
      ~f:(fun (before, d) ->
        let* member =
          Datatypes.member (before @ resource_types @ source.logical_types) d
        in
        Ok (d.Datatypes.module_name, member))
  in
  let* resource_members =
    all source.proof_resources ~f:(fun resource ->
        let at = resource.Source.resource_at in
        let l = loc at in
        let* library, arguments =
          match resource.resource_kind with
          | S.Resource_set elt ->
              let* elt = Source.ocaml_type source.env ~at elt in
              let* elt = Datatypes.typ types ~at elt in
              Ok ("SetRA", [ elt ])
          | Resource_auth base ->
              Ok ("Auth", [ R.Type.named ~loc:l (name ~loc:l base.pid_str) [] ])
        in
        let library = R.Name.make ~loc:l ~path:[ "Library" ] library in
        Ok
          ( resource.resource_name,
            R.Member.instance ~loc:l ~def:(library, arguments)
              (ident ~loc:l resource.resource_name)
              library ))
  in
  let proof_module_names =
    List.map source.proof_types ~f:(fun d -> d.Datatypes.module_name)
  in
  let runtime_modules =
    List.filter_map modules ~f:(fun (n, m) ->
        Option.some_if (not (List.mem proof_module_names n ~equal:String.equal)) m)
  in
  let proof_modules =
    List.filter_map source.proof ~f:(function
      | S.Proof_type { type_name; _ } ->
          List.Assoc.find modules
            (String.capitalize type_name.pid_str)
            ~equal:String.equal
      | Proof_resource { resource_name; _ } ->
          List.Assoc.find resource_members resource_name.pid_str ~equal:String.equal
      | _ -> None)
  in
  let modules = runtime_modules @ proof_modules in
  let* record_fields = Datatypes.fields types in
  let refs = ref [] in
  let primitives = ref [] in
  let pure = pure_functions funcs in
  let is_pure (f : func) = List.exists pure ~f:(fun g -> Ident.same g.id f.id) in
  (* A pure function's procedure is named apart from its function. *)
  let proc_name (f : func) = if is_pure f then f.raven_name ^ "_impl" else f.raven_name in
  let functions = List.map funcs ~f:(fun f -> (Ident.unique_name f.id, proc_name f)) in
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
  let* predicates = predicates source in
  (* The abstract predicates of the libraries, by their qualified names, as [Cell.holds],
     whose parameters' types are the library's own where it declares them. *)
  let* library_preds =
    all source.libraries ~f:(fun (lib : Source.library) ->
        let declared =
          List.concat_map lib.library.signature
            ~f:(fun (item : Parsetree.signature_item) ->
              match item.psig_desc with
              | Psig_type (_, decls) ->
                  List.map decls ~f:(fun (d : Parsetree.type_declaration) ->
                      d.ptype_name.txt)
              | _ -> [])
        in
        let rec qualify (t : S.pty) : S.pty =
          match t with
          | PTtyapp (Qid x, args) when List.mem declared x.pid_str ~equal:String.equal ->
              PTtyapp
                ( Qdot (Qid (S.mk_id ~loc:x.pid_loc lib.library_name), x),
                  List.map args ~f:qualify )
          | PTtyapp (q, args) -> PTtyapp (q, List.map args ~f:qualify)
          | PTtuple ts -> PTtuple (List.map ts ~f:qualify)
          | PTarrow (a, b) -> PTarrow (qualify a, qualify b)
          | PTtyvar _ -> t
        in
        all
          (List.filter (Annotation.of_comments lib.library.interface_comments)
             ~f:(fun a -> Poly.equal (Annotation.kind a) Annotation.Predicate))
          ~f:(fun a ->
            let* p = Annotation.predicate a in
            let* () =
              match p.pred_body with
              | Some _ -> unsupported a.loc "A predicate of a library with a definition"
              | None -> Ok ()
            in
            let* types =
              all p.pred_params ~f:(fun (_, t) ->
                  Source.ocaml_type source.env ~at:a.loc (qualify t))
            in
            Ok (lib, p, types)))
  in
  let library_preds = List.concat library_preds in
  let preds =
    List.map predicates ~f:(fun (_, p, _, types) ->
        (p.pred_name.pid_str, (p.pred_name.pid_str, types)))
    @ List.map library_preds ~f:(fun ((lib : Source.library), p, types) ->
        let key = lib.library_name ^ "." ^ p.pred_name.pid_str in
        (key, (key, types)))
  in
  let* logical_functions =
    all
      (List.filter source.proof ~f:(function S.Proof_function _ -> true | _ -> false))
      ~f:(function
        | S.Proof_function { function_name; function_params; function_result; _ } ->
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
                  lemma_inputs;
                  lemma_outputs = [ output ];
                } )
        | _ -> error Location.none "Expected a logical function declaration")
  in
  let proof_support =
    {
      resources = source.proof_resources;
      ghost_fields = source.proof_fields;
      logical_functions;
    }
  in
  let spec_funcs =
    List.map pure ~f:(fun f -> (Ident.name f.id, f.raven_name))
    @ List.map preds ~f:(fun (p, (raven, _)) -> (p, raven))
    @ List.map logical_functions ~f:(fun (n, s) -> (n, s.lemma_raven))
  in
  let lemma_declarations =
    List.filter source.proof ~f:(function S.Proof_lemma _ -> true | _ -> false)
  in
  let* () = check_lemma_recursion lemma_declarations in
  let* proof_lemmas =
    all lemma_declarations ~f:(function
      | S.Proof_lemma { lemma_name; lemma_params; lemma_returns; _ } ->
          let types_of ps =
            all ps ~f:(fun (id, ty) -> Source.ocaml_type ocaml_env ~at:id.S.pid_loc ty)
          in
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
                { lemma_raven = lemma_name.pid_str; lemma_inputs; lemma_outputs } )
      | _ -> error Location.none "Expected a lemma declaration")
  in
  let* () =
    match List.find_a_dup (List.map proof_lemmas ~f:fst) ~compare:String.compare with
    | None -> Ok ()
    | Some x -> error Location.none (Printf.sprintf "Duplicate lemma %s" x)
  in
  (* The views, with their values, and their ghost fields, on the structures. *)
  let views =
    List.filter_map predicates ~f:(fun (_, p, def, types) ->
        match def with
        | View { value } -> Some (p, value, types)
        | Body _ | Invariant _ -> None)
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
        Ok (anchor, (view_field p.pred_name.pid_str, typ, None)))
  in
  (* The structures with a state, and their histories, allocated empty. *)
  let actions =
    List.filter_map source.proof ~f:(function
      | Proof_action
          {
            action_name;
            action_params;
            action_step;
            action_consumes = _;
            action_state;
            action_update;
            action_linearizes;
            action_helps;
          } ->
          let id (x : S.id) = x.pid_str in
          let helps =
            Option.bind action_helps ~f:(fun (field, key, result) ->
                match field.term_desc with
                | Tfield (_, Qid f) -> Some (f.pid_str, key, result)
                | _ -> None)
          in
          Some
            {
              action = action_name.pid_str;
              params = List.map action_params ~f:id;
              step = Option.map action_step ~f:(fun (op, args) -> (op.pid_str, args));
              state = action_state.pid_str;
              update = List.map action_update ~f:(fun (f, t) -> (f.S.pid_str, t));
              linearizes = List.map action_linearizes ~f:id;
              helps;
              action_at = action_name.pid_loc;
            }
      | _ -> None)
  in
  let* structures =
    all
      (List.filter_map predicates ~f:(fun (at, p, def, param_types) ->
           match def with
           | Invariant { state; fields; body } ->
               Some (at, p, state, fields, body, param_types)
           | Body _ | View _ -> None))
      ~f:(fun (at, (p : S.predicate), state, state_fields, body, param_types) ->
        (* The key type of a field of pending calls. *)
        let pending_key t =
          match Datatypes.desc types t with
          | Tconstr (path, [ key ], _) when Path.same path source.pending -> Some key
          | _ -> None
        in
        let* fields =
          all state_fields ~f:(fun (sf : S.state_field) ->
              let* t = Source.ocaml_type ocaml_env ~at sf.sf_type in
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
                 match Source.ocaml_type ocaml_env ~at sf.sf_type with
                 | Ok t -> Option.map (pending_key t) ~f:(fun key -> (sf, key))
                 | Error _ -> None))
            ~f:(fun ((sf : S.state_field), key) ->
              let field = sf.sf_name.pid_str in
              let* helped =
                match sf.sf_helps with
                | Some f -> Ok f
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
            invariant = p.pred_name.pid_str;
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
            views = List.map views ~f:(fun (p, value, _) -> (p, value));
            at;
          })
  in
  let* structure_member_lists =
    all structures ~f:(fun st -> structure_members types st ~at:st.at)
  in
  let history_fields =
    List.filter_map structures ~f:(fun st ->
        Option.some_if (has_history st)
          (let l = R.Loc.none in
           let qn m x = R.Name.make ~loc:l ~path:[ m ] x in
           ( Option.value_map (anchor types st.structure_type) ~default:"" ~f:fst,
             ( member_name st "history",
               R.Type.named ~loc:l (R.Name.make ~loc:l (module_name st "history")) [],
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
  let shared =
    {
      persistent =
        List.filter_map predicates ~f:(fun (at, p, def, _) ->
            match def with
            | Invariant _ -> Some (p.pred_name.pid_str, at)
            | Body _ | View _ -> None);
      views =
        List.map views ~f:(fun (p, _, _) ->
            (p.pred_name.pid_str, view_field p.pred_name.pid_str));
      structures;
      anchors =
        List.map
          (List.dedup_and_sort (List.map view_fields ~f:fst) ~compare:String.compare)
          ~f:(fun anchor ->
            ( anchor,
              List.filter_map view_fields ~f:(fun (a, f) ->
                  Option.some_if (String.equal a anchor) f) ));
    }
  in
  (* The facts about earlier states in contracts, by the parameter they are about. *)
  let* pasts =
    all funcs ~f:(fun f ->
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
  (* Each library's module, trusted: its abstract predicates, and its values, as functions
     without arguments, and functions, as procedures with their contracts. *)
  let* library_modules =
    all source.libraries ~f:(fun (lib : Source.library) ->
        let l = loc Location.none in
        let own_preds =
          List.filter_map library_preds ~f:(fun ((lib' : Source.library), p, types) ->
              Option.some_if
                (String.equal lib'.library_name lib.library_name)
                ( p.pred_name.pid_str,
                  (lib.library_name ^ "." ^ p.pred_name.pid_str, types) ))
        in
        (* In the library's contracts, its predicates go by their own names. *)
        let ctx =
          spec_context types ~refs ~primitives ~shared ~ocaml_env
            ~preds:(own_preds @ preds)
            ~spec_funcs:
              (List.map own_preds ~f:(fun (p, (raven, _)) -> (p, raven)) @ spec_funcs)
            origins
        in
        let* pred_members =
          all
            (List.filter library_preds ~f:(fun ((lib' : Source.library), _, _) ->
                 String.equal lib'.library_name lib.library_name))
            ~f:(fun (_, (p : S.predicate), param_types) ->
              let* params =
                all (List.zip_exn p.pred_params param_types) ~f:(fun ((x, _), t) ->
                    let* typ = Datatypes.typ types ~at:x.S.pid_loc t in
                    Ok (t, R.Var.make ~loc:l (ident ~loc:l x.pid_str) typ))
              in
              (* The trailing parameters without references are outputs, as for the
                 program's predicates; a library's abstract type may have references. *)
              let outputs =
                let n =
                  List.length
                    (List.take_while (List.rev params) ~f:(fun (t, _) ->
                         not (Datatypes.has_refs types t)))
                in
                if n = List.length params then 0 else n
              in
              let inputs, outputs = List.split_n params (List.length params - outputs) in
              Ok
                (R.Member.free
                   (R.Member.callable
                      (R.Callable.func ~loc:l ~kind:Pred ~formals:(List.map inputs ~f:snd)
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
                  let value =
                    Env.find_value (Pdot (Pident lib.library_id, x)) source.env
                  in
                  let rec arrows (t : Types.type_expr) =
                    match Types.get_desc t with
                    | Tarrow (Nolabel, a, r, _) ->
                        let args, result = arrows r in
                        (a :: args, result)
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
  (* The checks that the actions keep the histories' orders. *)
  let* action_check_lists =
    all structures ~f:(fun st ->
        action_checks
          (spec_context types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
             origins)
          st)
  in
  let* pending_member_lists =
    all structures ~f:(fun st ->
        all st.pendings ~f:(fun p ->
            match
              List.find funcs ~f:(fun f -> String.equal (Ident.name f.id) p.helped)
            with
            | Some helped ->
                pending_members
                  (spec_context types ~refs ~primitives ~shared ~ocaml_env ~preds
                     ~spec_funcs origins)
                  st p helped ~helped_proc:(proc_name helped)
            | None ->
                error st.at (Printf.sprintf "There is no function %s to help" p.helped)))
  in
  let* pred_members =
    all predicates ~f:(fun (at, p, def, param_types) ->
        predicate types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
          ~proof_support origins ~at
          ~views:(List.map views ~f:(fun (p, value, _) -> (p, value)))
          ~structures p def param_types)
  in
  let predicate_bodies =
    List.filter_map predicates ~f:(fun (_, p, definition, _) ->
        match definition with
        | Body body -> Some (p.S.pred_name.pid_str, body)
        | Invariant _ | View _ -> None)
  in
  let* lemma_members =
    all lemma_declarations
      ~f:
        (proof_lemma types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
           ~proof_lemmas ~proof_support ~predicate_bodies origins)
  in
  let* logical_members =
    all
      (List.filter_mapi source.proof ~f:(fun i declaration ->
           match declaration with
           | S.Proof_function _ -> Some (i, declaration)
           | _ -> None))
      ~f:(fun (i, declaration) ->
        let previous =
          List.filter_map (List.take source.proof i) ~f:(function
            | S.Proof_function { function_name; _ } -> Some function_name.pid_str
            | _ -> None)
        in
        let logical_functions =
          List.filter logical_functions ~f:(fun (n, _) ->
              List.mem previous n ~equal:String.equal)
        in
        let spec_funcs =
          List.filter spec_funcs ~f:(fun (n, _) ->
              (not (List.Assoc.mem proof_support.logical_functions n ~equal:String.equal))
              || List.mem previous n ~equal:String.equal)
        in
        proof_function types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs
          ~proof_support:{ proof_support with logical_functions }
          origins declaration)
  in
  let* pure_funcs =
    all pure
      ~f:
        (func types ~refs ~primitives ~shared ~ocaml_env ~preds
           ~funcs:(List.map pure ~f:(fun f -> (Ident.unique_name f.id, f.raven_name)))
           ~spec_funcs ~proof_support origins)
  in
  let* procs =
    all funcs ~f:(fun f ->
        proc types ~refs ~primitives ~shared ~ocaml_env ~preds ~funcs:spec_funcs
          ~annotations ~linearizations ~lifted ~pasts ~past_returns ~ghost_args
          ~proof_lemmas ~proof_support
          ~libraries:
            (List.map source.libraries ~f:(fun (lib : Source.library) ->
                 (lib.library_id, lib.library_name)))
          functions origins ~proc_name:(proc_name f) ~pure:(is_pure f) f)
  in

  let file_start = { Lexing.dummy_pos with pos_fname = source.file } in
  let start = R.Loc.make file_start file_start in
  let ref_fields = List.map !refs ~f:snd in
  let ghost_fields =
    List.filter_map view_fields ~f:(fun (_, (field, typ, init)) ->
        Option.some_if (Option.is_none init)
          (R.Member.field ~loc:start ~ghost:true (ident ~loc:start field) typ))
  in
  let* explicit_fields =
    all source.proof_fields ~f:(fun field ->
        let l = loc field.Source.field_at in
        let* value_type = Datatypes.typ types ~at:field.field_at field.field_value in
        Ok
          (R.Member.field ~loc:l ~ghost:true
             (ident ~loc:l (ghost_field_name field))
             value_type))
  in
  Ok
    ( R.Program.make ~loc:start
        (Prelude.members @ modules @ library_modules @ record_fields @ ref_fields
       @ ghost_fields @ explicit_fields
        @ List.concat structure_member_lists
        @ List.concat_map pending_member_lists ~f:List.concat
        @ List.concat action_check_lists
        @ List.map !primitives ~f:snd
        @ List.map
            (logical_members @ pred_members @ pure_funcs @ lemma_members)
            ~f:R.Member.callable
        @ List.map2_exn funcs procs ~f:(fun f p ->
            (* A trusted function's procedure is assumed. *)
            if f.trusted then R.Member.free (R.Member.callable p) else R.Member.callable p)
        ),
      !origins )
