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
  | Unknown

(** How the atomic update closes. *)
type au_close =
  | Commit  (** The step linearized the function. *)
  | Abort  (** The step did not change the abstract state. *)
  | Commit_call  (** The step is a call, which linearized the function in its place. *)

type action = {
  action : string;
  params : string list;
  step : (string * S.term option list) option;
      (** The operation performing it, with its arguments: the location, then the others,
          [None] for any. *)
  state : string;
  update : (string * S.term) list;  (** The fields it changes. *)
  linearizes : string list;
}
(** An action of a structure (see {!S.Proof_action}). *)

type performing = { performed : action; bindings : (string * R.Expr.t) list }
(** An action that a step performs, with the values of its parameters. *)

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
}
(** The atomic update of a function with an atomic contract. *)

type structure = {
  invariant : string;
  state : string;
  fields : (string * string * R.Type.t * Types.type_expr * bool) list;
  chains : (string * string) list;
  actions : action list;
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
  lifted : (string * (Ident.t list * string option)) list;
      (** The lifted local functions, by their procedures' names, with the parameters of
          the function they continue, which their calls pass first, and its name. *)
  origins : origin list ref;
  annotations : Annotation.t list;  (** Those of the file, as loops' invariants. *)
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

(** The functions of OCaml's standard library on lists that contracts can use, as Raven's
    [List]'s. *)
let list_function : S.qualid -> string option = function
  | Qdot (Qid { pid_str = "List"; _ }, { pid_str = "length"; _ }) -> Some "len"
  | Qdot (Qid { pid_str = "List"; _ }, { pid_str = "mem"; _ }) -> Some "in"
  | _ -> None

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

(** The names that the contract term [t] uses free. *)
let rec term_names (t : S.term) : string list =
  let rec pat_names (p : S.pat) =
    match p.pat_desc with
    | Pwild | Pconst _ | Pconstr (_, None) -> []
    | Pid id -> [ id.pid_str ]
    | Ptuple ps -> List.concat_map ps ~f:pat_names
    | Pcast (p, _) | Pconstr (_, Some p) -> pat_names p
  in
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
    | Tquant (_, _, t) | Tattr (_, t) | Tcast (t, _) | Told t | Tfield (t, _) -> find t
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
      | Tvar (Qid { pid_str = p; _ }) ->
          begin match List.Assoc.find env.ctx.preds p ~equal:String.equal with
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
                Ok (id.pid_str, t, R.Var.make ~loc:l (ident ~loc:l id.pid_str) ty))
      in
      let env =
        List.fold bound ~init:env ~f:(fun env (x, t, _) ->
            { (bind env x (Raven x)) with var_types = (x, t) :: env.var_types })
      in
      let* body = formula env body in
      let vars = List.map bound ~f:(fun (_, _, v) -> v) in
      (* A variable of type [int] ranges over its values. *)
      let ranges =
        List.filter_map bound ~f:(fun (x, t, _) ->
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
  | Tattr (_, t) | Tcast (t, _) -> formula env t
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
            Option.bind (List.Assoc.find env.var_types x ~equal:String.equal) ~f:(fun t ->
                Option.map (field_type env.ctx t label) ~f:(fun _ -> x))
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
  | Tlet _ | Told _ -> unsupported at "This formula"

(** The formula [t], a sequence if it is a list literal and [expected] is a sequence type,
    as [[]] in [queue q []]. *)
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
  | Tvar (Qid { pid_str = x; _ }), _ ->
      List.Assoc.find env.var_types x ~equal:String.equal
  | _, ({ term_desc = Tvar (Qid { pid_str = "drop" | "take"; _ }); _ }, [ _; s ]) ->
      term_type env s
  | _, ({ term_desc = Tvar (Qid { pid_str = "++"; _ }); _ }, [ a; b ]) ->
      Option.first_some (term_type env a) (term_type env b)
  | Tfield ({ term_desc = Tvar (Qid { pid_str = x; _ }); _ }, Qid { pid_str = f; _ }), _
    ->
      Option.bind (state_fields env x) ~f:(fun fields ->
          Option.map (List.Assoc.find fields f ~equal:String.equal) ~f:snd)
  | _, ({ term_desc = Tvar (Qid { pid_str = "([])" | "last"; _ }); _ }, s :: _) ->
      (* An entry of a sequence. *)
      begin match Option.map (term_type env s) ~f:(Datatypes.desc env.data) with
      | Some (Tconstr (_, [ elt ], _)) -> Some elt
      | _ -> None
      end
  | _ -> None

(** The OCaml type of the values that the location [t] holds, where it is known. *)
and location_type env (t : S.term) =
  match t.term_desc with
  | Tfield ({ term_desc = Tvar (Qid { pid_str = x; _ }); _ }, Qid { pid_str = label; _ })
    ->
      Option.bind (List.Assoc.find env.var_types x ~equal:String.equal) ~f:(fun ty ->
          field_type env.ctx ty label)
  | Tvar (Qid { pid_str = x; _ }) ->
      Option.bind (List.Assoc.find env.var_types x ~equal:String.equal) ~f:(fun ty ->
          field_type env.ctx ty "")
  | _ -> None

(** The application [t] of an operator or a constructor. *)
and application env (t : S.term) =
  let at = t.term_loc in
  let l = loc at in
  let head, args = spine t [] in
  match (head.term_desc, args) with
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
  | Tvar (Qid { pid_str = f; _ }), _ :: _
    when List.Assoc.mem env.funcs f ~equal:String.equal ->
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
      Ok (R.Expr.call ~loc:l (name ~loc:l func) args)
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
  match t.term_desc with
  | Tfield ({ term_desc = Tvar (Qid { pid_str = x; _ }); _ }, Qid { pid_str = label; _ })
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
          | None, None -> error at (Printf.sprintf "%s has no mutable field %s" x label)
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
          unsupported at "This location, other than a field of a variable or an atomic,"
    end

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
    data = ctx.types;
    funcs = ctx.spec_funcs;
    vars = List.map scope ~f:(fun (x, (raven, _)) -> (x, Raven raven));
  }

(** The ghost statements in the annotations between the positions [after] and [before], as
    [e1; (*@ unfold p x *) e2]. *)
let ghost ctx ~(after : Lexing.position) ~(before : Lexing.position) =
  let between (a : Annotation.t) =
    a.loc.loc_start.pos_cnum >= after.pos_cnum
    && a.loc.loc_end.pos_cnum <= before.pos_cnum
    && Poly.equal (Annotation.kind a) Annotation.Ghost
  in
  let* stmts = all (List.filter ctx.annotations ~f:between) ~f:Annotation.ghost_stmts in
  let env = scope_env ctx in
  let use (t : S.term) make =
    let head, args = spine t [] in
    match head.term_desc with
    | Tvar (Qid { pid_str = p; _ }) when List.Assoc.mem ctx.preds p ~equal:String.equal ->
        let raven, _ = List.Assoc.find_exn ctx.preds p ~equal:String.equal in
        let* args = all args ~f:(formula env) in
        let l = loc t.term_loc in
        Ok (make ~loc:l (name ~loc:l raven) args)
    | _ -> error t.term_loc "Expected a predicate applied to its arguments"
  in
  all (List.concat stmts) ~f:(function
    | S.Fold t -> use t (fun ~loc p args -> R.Stmt.fold ~loc p args)
    | Unfold t -> use t (fun ~loc p args -> R.Stmt.unfold ~loc p args)
    | Assert t ->
        let* c = formula env t in
        Ok (R.Stmt.assert_ ~loc:(loc t.term_loc) (R.Spec.make c)))

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

(** The statements opening the invariants the function holds before the step at [at], or
    with [fold] closing them after it, where a failure is reported. *)
let use_invariants ?performs ctx ~(at : Location.t) ~fold =
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
          let fold ?(witnesses = []) () =
            [ R.Stmt.fold ~loc:la ~witnesses (name ~loc:la inv) args ]
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
              begin match performs with
              | Some p ->
                  (* The action's state, which the history learns if a growing field
                     changes, and the fields it changes, as witnesses. *)
                  let next, indices, appended =
                    next_state ctx st ~inv_params:st.params args opened p
                  in
                  let values = List.map next ~f:fst in
                  let grows =
                    List.exists2_exn st.fields next
                      ~f:(fun (_, _, _, _, grows) (_, changes) -> grows && changes)
                  in
                  let witnesses =
                    List.filter_map (List.zip_exn st.fields next)
                      ~f:(fun ((_, raven, _, _, _), (e, changes)) ->
                        Option.some_if changes (ident ~loc:la raven, e))
                    @ List.map indices ~f:(fun (index, e) -> (ident ~loc:la index, e))
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
                            let index =
                              List.Assoc.find_exn st.chains field ~equal:String.equal
                            in
                            ( field,
                              Option.value
                                (List.Assoc.find indices index ~equal:String.equal)
                                ~default:e ));
                    }
                  in
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
                  if has_history st then learn @ (snapshot st state :: fold ~witnesses ())
                  else fold ~witnesses ()
              | None when has_history st -> snapshot st opened :: fold ()
              | None -> fold ()
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
          let env =
            bind (scope_env ctx) st.state
              (State
                 (List.map2_exn st.fields next ~f:(fun (f, _, _, t, _) (e, _) ->
                      (f, (e, t)))))
          in
          let* views =
            all st.views ~f:(fun ((v : S.predicate), value) ->
                let pred = v.pred_name.pid_str in
                let inputs = List.take args (List.length v.pred_params - 1) in
                let env =
                  List.fold2_exn (List.drop_last_exn v.pred_params) inputs ~init:env
                    ~f:(fun env (id, _) e -> bind env id.S.pid_str (Value e))
                in
                let* value = formula env value in
                let raven, _ = List.Assoc.find_exn ctx.preds pred ~equal:String.equal in
                Ok
                  (with_views ctx
                     (fun ~loc ~pred:_ p args -> [ R.Stmt.fold ~loc p args ])
                     ~loc:l ~pred (name ~loc:l raven) (inputs @ [ value ])))
          in
          Ok (List.concat views)
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
                    Ok
                      (List.fold (List.filter_opt equalities)
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

(** The annotation saying how the atomic step at [at] linearizes the function, if one
    follows it, as [Atomic.get t (*@ commit *)]. *)
let linearization ctx ~(at : Location.t) =
  match
    List.find ctx.linearizations ~f:(fun (anchor, _) -> anchor = at.loc_end.pos_cnum)
  with
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

(** The statements of [access], an atomic step, inside the atomic update of a function
    with an atomic contract that has not linearized yet. The step linearizes the function
    as [how] says: always, never, if it is a [compare_and_set] that succeeds, or if it is
    a read whose value has a constructor. *)
let linearize ?step ctx ~at (how : [ `Commit | `Abort | `Cas | `Returning of string ])
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
        let close ?performs () =
          ctx.snapshots <- snapshots;
          use_invariants ?performs ctx ~at ~fold:true
        in
        let unchanged = close () in
        let performed =
          List.fold_right performings ~init:unchanged ~f:(fun (p, condition) rest ->
              [ R.Stmt.if_ ~loc:l condition (close ~performs:p ()) rest ])
        in
        let failed = close () in
        ctx.snapshots <- snapshots;
        opening @ access @ snapshot
        @ [ R.Stmt.if_ ~loc:l result [ R.Stmt.ghost_block ~loc:l performed ] failed ]
  in
  match ctx.au with
  | None -> Ok (around access)
  | Some au ->
      begin match au.state with
      | Committed -> Ok (around access)
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
  let* annotation = linearization ctx ~at in
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
    | Some (Returning { pat_desc = Pconstr (Qid c, _); _ }), `Abort ->
        Ok (`Returning c.pid_str)
    | Some (Returning p), `Abort ->
        unsupported p.pat_loc "A pattern other than a constructor, after returning,"
    | Some (Returning p), _ -> error p.pat_loc "Only a read can linearize by its value"
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
      let* step =
        linearize ctx ~at how (R.Stmt.local ~loc:l ~typ ~init:read (ident ~loc:l x))
      in
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
      | _ -> unsupported at ("A call of " ^ Path.name path))
  | _ -> unsupported at "This application"

(** The call of the top-level function [f] with [args], in [e]: a statement, whose result
    is kept in a variable unless it is unit. *)
and call ctx (e : Typedtree.expression) f args =
  let l = loc e.exp_loc in
  let* stmts_args = all (List.rev args) ~f:(fun arg -> expr ctx arg) in
  let stmts = List.concat_map stmts_args ~f:fst in
  let args = List.rev_map stmts_args ~f:snd in
  (* A lifted local function takes the parameters of the function it continues first. *)
  let prefix, role =
    Option.value (List.Assoc.find ctx.lifted f ~equal:String.equal) ~default:([], None)
  in
  let* prefix =
    all prefix ~f:(fun id ->
        match Names.find ctx.names id with
        | Some x -> Ok (R.Expr.var ~loc:l (name ~loc:l x))
        | None ->
            error e.exp_loc (Printf.sprintf "%s is not in scope here" (Ident.name id)))
  in
  let args = prefix @ args in
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
        | Committing | On_cas | On_read _ | Partly | Unknown ->
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
  let callee =
    R.Expr.call ~loc:l (name ~loc:l f) (args @ List.concat witnesses @ implicit)
  in
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
      (** The parameters of the function that a lifted local function continues, which its
          parameters start with. *)
  role : string option;  (** The function whose atomic update it continues. *)
}
(** A top-level function [f] with its parameters [params] and [body], and its contract, or
    a local function lifted to the top level. *)

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
        | Lunit _ | Lwild -> Ok None
        | Lghost (id, _) -> unsupported id.pid_loc "A ghost argument"
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
    their declarations. *)
let formals ctx (f : func) =
  all f.params ~f:(fun (p : Typedtree.function_param) ->
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
      | _ -> unsupported p.fp_loc "This parameter")

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
      data = ctx.types;
      funcs = spec_funcs;
      vars = List.map named ~f:(fun (x, r, _) -> (x, Raven r));
    }
  in
  let env = pattern_definitions env f in
  let* implicit = implicit_vars env f in
  let env =
    List.fold implicit ~init:env ~f:(fun env (x, raven, t, _) ->
        { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
  in
  Ok (result_name, env, implicit)

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
let func types ~refs ~primitives ~shared ~ocaml_env ~preds ~funcs ~spec_funcs origins
    (f : func) : (R.Callable.t, error) Result.t =
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
    }
  in
  let l = loc f.loc in
  let* formals = formals ctx f in
  let result = Names.fresh ctx.names "result" in
  let* _, env, implicit = contract_env ctx ~spec_funcs f formals ~result in
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
    }
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
                    @ indices)
                  (name ~loc:l inv) args;
              ])
    end

(** The procedure of [f], named [proc_name]; if [f] is pure, its result is the value of
    its function. [funcs] are the functions contracts can call, by their OCaml names. *)
let proc types ~refs ~primitives ~shared ~ocaml_env ~preds ~funcs ~annotations
    ~linearizations ~lifted ~pasts ~past_returns (functions : (string * string) list)
    origins ~proc_name ~pure (f : func) : (R.Callable.t, error) Result.t =
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
      origins;
      annotations;
      spec_funcs = funcs;
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
  let* formals = formals ctx f in
  let header = Option.bind f.contract ~f:(fun c -> c.header) in
  let* result_name, _ = contract_names f header (List.length formals) in
  let result = Names.fresh names result_name in
  let* returns =
    if is_unit f.body.exp_type then Ok []
    else
      let* typ = typ ctx ~at:f.body.exp_loc f.body.exp_type in
      Ok [ R.Var.make ~loc:l (ident ~loc:l result) typ ]
  in
  let* _, env, implicit = contract_env ctx ~spec_funcs:funcs f formals ~result in
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
        (Option.value_map f.next ~default:{ f.loc.loc_end with pos_cnum = Int.max_value }
           ~f:(fun l -> l.loc_start))
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
           step that linearizes it there, as (*@ commit *) or (*@ returning [] -> commit \
           *)"
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
                Printf.sprintf "The invariant %s may not hold when this function returns"
                  inv;
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
  let body = bind_au @ first @ stmts @ assignment @ establish @ last in
  Ok
    (R.Callable.proc ~loc:l
       ~formals:(List.map formals ~f:(fun (_, _, v) -> v) @ past_formals @ implicit)
       ~returns:(returns @ past_returns) ~requires ~ensures (ident ~loc:l proc_name)
       (Some body))

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
  let item ((item : Typedtree.structure_item), next) =
    match item.str_desc with
    | Tstr_type (_, decls) ->
        let* types = all decls ~f:Datatypes.of_declaration in
        Ok (types, [])
    | Tstr_value (_, bindings) ->
        let* funcs =
          all bindings ~f:(fun (vb : Typedtree.value_binding) ->
              match (vb.vb_pat.pat_desc, vb.vb_expr.exp_desc) with
              | Tpat_var (id, _, _), Texp_function (params, Tfunction_body body) ->
                  let* contract =
                    contract_after annotations ~item_loc:item.str_loc ~next
                  in
                  let* contract =
                    match
                      ( contract,
                        List.Assoc.find interface (Ident.name id) ~equal:String.equal )
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
                      raven_name = Ident.name id;
                      params;
                      body;
                      loc = vb.vb_loc;
                      contract;
                      next;
                      prefix = [];
                      role = None;
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
    | Tpat_var (id, _, _) | Tpat_alias (_, id, _, _, _) -> found := id :: !found
    | _ -> ()
    end;
    Tast_iterator.default_iterator.pat iterator p
  in
  ({ Tast_iterator.default_iterator with pat }, found)

(** The identifiers that the patterns of [e] bind, its functions' parameters included. *)
let bound_in (e : Typedtree.expression) : Ident.t list =
  let iterator, found = binders () in
  iterator.expr iterator e;
  !found

(** The identifiers that the parameters [params] bind, in order. *)
let params_bound (params : Typedtree.function_param list) : Ident.t list =
  let iterator, found = binders () in
  List.iter params ~f:(fun p ->
      match p.fp_kind with
      | Tparam_pat pat -> iterator.pat iterator pat
      | Tparam_optional_default (pat, _) -> iterator.pat iterator pat);
  List.rev !found

(** The local functions of the top-level function [outer], lifted to the top level, with
    their contracts in [annotations]: one after the function's definition, before the
    expression it is local to. A function that [continues] [outer] takes [outer]'s
    parameters first and has its contract too; another may not use [outer]'s variables. *)
let local_functions (outer : func) (annotations : Annotation.t list) =
  let found = ref [] in
  let expr iterator (e : Typedtree.expression) =
    begin match e.exp_desc with
    | Texp_let (_, [ vb ], rest) ->
        begin match (vb.vb_pat.pat_desc, vb.vb_expr.exp_desc) with
        | Tpat_var (id, _, _), Texp_function (params, Tfunction_body body) ->
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
      let* () =
        match captured with
        | x :: _ ->
            unsupported vb.vb_loc
              (Printf.sprintf "A local function using the variable %s of its context,"
                 (Ident.name x))
        | [] -> Ok ()
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
                hd_args = names outer.params oc.header @ names params c.header;
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
        | _ -> contract
      in
      let prefix_params =
        List.filter outer.params ~f:(fun p ->
            match p.fp_kind with
            | Tparam_pat { pat_desc = Tpat_var (x, _, _); _ } ->
                List.mem prefix x ~equal:Ident.same
            | _ -> false)
      in
      Ok
        {
          id;
          raven_name = Ident.name id;
          params = prefix_params @ params;
          body;
          loc = vb.vb_loc;
          contract;
          next = Some rest.exp_loc;
          prefix;
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
        found := e.exp_loc.loc_end.pos_cnum :: !found
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

(** The conjuncts of [t]. *)
let rec conjuncts (t : S.term) =
  let t = S.chain t in
  match spine t [] with
  | { term_desc = Tvar (Qid { pid_str = "&&" | "/\\"; _ }); _ }, [ a; b ] ->
      conjuncts a @ conjuncts b
  | _ -> [ t ]

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
  (* Sequences grow by prefix, integers by <=. *)
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
      data = ctx.types;
      funcs = ctx.spec_funcs;
      vars = List.map params ~f:(fun (x, raven, _, _) -> (x, Raven raven));
    }
  in
  Ok (params, env)

(** The predicate [p], declared at [at], whose parameters have the OCaml types
    [param_types], defined as [def]; [views] are the views of the program, for an
    invariant to hold its half of each. *)
let predicate types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs origins ~at
    ~views ~structures (p : S.predicate) (def : definition) param_types :
    (R.Callable.t, error) Result.t =
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
    }
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
      let body = List.reduce_exn body ~f:(bin And) in
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
      let existentials =
        List.map st.fields ~f:(fun (_, raven, typ, _, _) ->
            R.Var.make ~loc:l (ident ~loc:l raven) typ)
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
      | Proof_state _ | Proof_action _ -> Ok None
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

(** The Raven program of [source]. *)
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
  let steps = atomic_steps source.typed in
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
  let* types, funcs = items ~interface source.typed annotations in
  let* lifted = all funcs ~f:(fun f -> local_functions f annotations) in
  let funcs = funcs @ List.concat lifted in
  (* The data types, and the sequences of specifications, which have no module. *)
  let data_types = types in
  let types =
    types @ match source.sequence with Pident id -> [ Datatypes.sequence id ] | _ -> []
  in
  (* Each data type's module, given the ones declared before it; a record type that is a
     reference has fields instead. *)
  let* modules =
    all
      (List.filter_mapi data_types ~f:(fun i (d : Datatypes.t) ->
           Option.some_if
             (Option.is_none d.heap && Option.is_none d.alias)
             (List.take data_types i, d)))
      ~f:(fun (before, d) -> Datatypes.member before d)
  in
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
          ((not (List.is_empty f.prefix)) || Option.is_some f.role)
          (proc_name f, (f.prefix, f.role)))
  in
  let origins = ref [] in
  let ocaml_env = source.env in
  (* The predicates' signatures first, for their bodies and the contracts to use. *)
  let* predicates = predicates source in
  let preds =
    List.map predicates ~f:(fun (_, p, _, types) ->
        (p.pred_name.pid_str, (p.pred_name.pid_str, types)))
  in
  let spec_funcs =
    List.map pure ~f:(fun f -> (Ident.name f.id, f.raven_name))
    @ List.map preds ~f:(fun (p, (raven, _)) -> (p, raven))
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
          } ->
          let id (x : S.id) = x.pid_str in
          Some
            {
              action = action_name.pid_str;
              params = List.map action_params ~f:id;
              step = Option.map action_step ~f:(fun (op, args) -> (op.pid_str, args));
              state = action_state.pid_str;
              update = List.map action_update ~f:(fun (f, t) -> (f.S.pid_str, t));
              linearizes = List.map action_linearizes ~f:id;
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
      ~f:(fun (at, (p : S.predicate), state, fields, body, param_types) ->
        let* fields =
          all fields ~f:(fun (sf : S.state_field) ->
              let* t = Source.ocaml_type ocaml_env ~at sf.sf_type in
              let* typ = Datatypes.typ types ~at t in
              Ok
                (sf.sf_name.pid_str, state ^ "_" ^ sf.sf_name.pid_str, typ, t, sf.sf_grows))
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
  let* pred_members =
    all predicates ~f:(fun (at, p, def, param_types) ->
        predicate types ~refs ~primitives ~shared ~ocaml_env ~preds ~spec_funcs origins
          ~at
          ~views:(List.map views ~f:(fun (p, value, _) -> (p, value)))
          ~structures p def param_types)
  in
  let* pure_funcs =
    all pure
      ~f:
        (func types ~refs ~primitives ~shared ~ocaml_env ~preds
           ~funcs:(List.map pure ~f:(fun f -> (Ident.unique_name f.id, f.raven_name)))
           ~spec_funcs origins)
  in
  let* procs =
    all funcs ~f:(fun f ->
        proc types ~refs ~primitives ~shared ~ocaml_env ~preds ~funcs:spec_funcs
          ~annotations ~linearizations ~lifted ~pasts ~past_returns functions origins
          ~proc_name:(proc_name f) ~pure:(is_pure f) f)
  in

  let file_start = { Lexing.dummy_pos with pos_fname = source.file } in
  let start = R.Loc.make file_start file_start in
  let ref_fields = List.map !refs ~f:snd in
  let ghost_fields =
    List.filter_map view_fields ~f:(fun (_, (field, typ, init)) ->
        Option.some_if (Option.is_none init)
          (R.Member.field ~loc:start ~ghost:true (ident ~loc:start field) typ))
  in
  Ok
    ( R.Program.make ~loc:start
        (Prelude.members @ modules @ record_fields @ ref_fields @ ghost_fields
        @ List.concat structure_member_lists
        @ List.map !primitives ~f:snd
        @ List.map (pred_members @ pure_funcs @ procs) ~f:R.Member.callable),
      !origins )
