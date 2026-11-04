(** The translation's shared state and helpers: the contexts of contracts and procedures,
    Raven names, fields and primitives, and generated checks. *)

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

type performing = {
  performed : action;
  bindings : (string * R.Expr.t) list;
  invariant : string option;
      (** The instance matched by the step; absent for an unresolved named action. *)
}
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

type domain_request = { domain_types : Datatypes.t list; domain_type : Types.type_expr }

type function_instance = {
  instance_namespace : string list;
  instance_name : string;
  instance_worker : string;
  instance_arguments : string list;
}

type default_request = {
  default_namespace : string list;
  default_name : string;
  default_type : R.Type.t;
}

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

(** How a function that commits its atomic update ends: returning, raising an exception
    with its value and constructor's name if known, or with the outcome of a call that
    committed in its place. *)
and au_outcome = Returned | Raised of R.Expr.t * string option | Outcome of R.Expr.t

(** The state of a translation, threaded explicitly: what each arm of a branch starts
    from, what carries on from arm to arm within a procedure, the supply of fresh names,
    the fields and primitives used, and the checks generated: the monad, without the
    operations that use a context's inputs, which {!State} adds. *)
module State_monad = struct
  type au_path = {
    au_state : au_state;
    au_step : Location.t;  (** The step that opened the update. *)
    au_values : R.Expr.t list;
        (** The values of the implicit parameters in the update. *)
    au_performing : (performing * R.Expr.t option) option;
        (** The action that the step performs if it commits, as [(*@ performs pop *)] or
            by its step, with the condition, if any, under which the step is the action's.
        *)
  }
  (** The part of an atomic update that each arm of a branch starts from. *)

  type au_results = {
    cas_results : (string * bool) list;
        (** Variables bound to the result of a [compare_and_set], or its negation if
            [false], by their unique names. *)
    read_results : string list;
        (** Variables bound to the value of the last read, by their unique names. *)
  }
  (** The part of an atomic update that carries on from arm to arm. *)

  type path = {
    opened : (string * opened) list;
    unfolded : (string * string list) list;
        (** The parts of each open invariant unfolded with it, by their predicates. *)
    snapshots : (string * opened list) list;
    positions : position list;
    au : au_path option;
  }
  (** What each arm of a branch starts from. *)

  (** The exceptions a function may raise: those named, or any. *)
  type raise_set = Raises of string list | Raises_any

  type exit = {
    results : R.Expr.t list;
        (** The function's return values before its outcome, returned as they are when it
            raises. *)
    allowed : raise_set;
    raises_terms : S.term list;
        (** What holds when it raises, over [outcome_name], as its contract says. *)
  }
  (** How a function that may raise leaves when it raises. *)

  type handler = {
    outcome : R.Expr.t;
        (** The variable of the exception raised in its protected part. *)
    outcome_type : R.Type.t;
    reaching : raise_set;  (** The exceptions its protected part may raise so far. *)
  }
  (** An exception handler whose protected part is being translated. *)

  type carried = {
    exit : exit option;
    handlers : handler list;  (** The enclosing handlers, innermost first. *)
    pending : R.Stmt.t list;
        (** The points after which an exception may be pending for the innermost handler:
            [nest] guards the statements after them. *)
    caught : (Ident.t * raise_set) list;
        (** The variables that handler patterns bind, with the exceptions they hold. *)
    ghost_returns : (string * string * Types.type_expr) list;
    proof_state : (R.Expr.t * Types.type_expr) option;
    outline_exports : (string * (R.Expr.t * Types.type_expr)) list;
        (** The values that steps of the function's outline exported, by their keys. *)
    return_covered : bool;
    fields_of : (string * (string * R.Expr.t)) list;
    formals : R.Expr.t list;
    facts : R.Spec.t list;
    invariants : (string * R.Expr.t list) list;
    au_results : au_results option;
  }
  (** What carries on from arm to arm within a procedure. *)

  type names = {
    used : Set.M(String).t;
    bound : (string * string) list;
    scope : (string * (string * Types.type_expr option)) list;
  }

  type primitive_operation =
    | Atomic of Primitives.op
    | Ordinary of Primitives.ordinary_op

  type primitive_key = {
    field : string;
    payload : Datatypes.type_key;
    operation : primitive_operation;
    exact : bool;
    bounded : bool;
    admissibility : string option;
  }

  type primitive = { key : primitive_key; name : string; member : R.Member.t }

  type tables = {
    primitives : (string list * primitive list) list;
        (** The atomic operations used so far, by the namespace they are declared in, and
            by their names (see {!Primitives}). *)
    domains : domain_request list;
    dictionaries : domain_request list;
    function_instances : function_instance list;
    call_targets : (string list * string) list;
    defaults : default_request list;
    dynamic_indices : bool;
        (** Whether an invariant is established with index maps that are computed. *)
  }

  type state = {
    path : path;
    carried : carried;
    names : names;
    tables : tables;
    origins : origin list;  (** The checks generated so far, latest first. *)
    warnings : R.Diagnostic.t list;
  }

  type 'a t = state -> ('a, error) Result.t * state
  (** A computation on the state: its result, and its state at the end, which on an error
      is the state when it failed, as with mutable state. *)

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

  open Syntax

  let note_families types requested =
    let instances = Datatypes.family_dependencies types requested in
    let* () =
      match
        List.find instances ~f:(fun instance ->
            List.is_prefix instance.Datatypes.family_namespace
              ~prefix:(String.split instance.family_worker ~on:'.')
              ~equal:String.equal
            && not (String.equal instance.family_name instance.family_worker))
      with
      | None -> return ()
      | Some instance ->
          let at =
            Option.value_map
              (List.find types ~f:(fun data ->
                   Option.exists data.Datatypes.family ~f:(fun family ->
                       String.equal family.worker instance.family_worker)))
              ~default:Location.none
              ~f:(fun data -> data.Datatypes.at)
          in
          of_result (unsupported at "A nonregular cyclic generic family")
    in
    modify (fun state ->
        let function_instances =
          List.fold instances ~init:state.tables.function_instances
            ~f:(fun previous instance ->
              if
                String.equal instance.Datatypes.family_name instance.family_worker
                || List.exists previous ~f:(fun previous ->
                    String.equal
                      (String.concat ~sep:"."
                         (previous.instance_namespace @ [ previous.instance_name ]))
                      instance.family_name)
              then previous
              else
                previous
                @ [
                    {
                      instance_namespace = instance.family_namespace;
                      instance_name = (Qualified_name.of_string instance.family_name).name;
                      instance_worker = instance.family_worker;
                      instance_arguments = instance.family_arguments;
                    };
                  ])
        in
        let dictionaries =
          List.fold
            (requested @ Datatypes.family_argument_types types requested)
            ~init:state.tables.dictionaries
            ~f:(fun previous typ ->
              if List.is_empty instances then previous
              else if
                List.exists previous ~f:(fun request ->
                    Option.equal String.equal
                      (Datatypes.dictionary_name request.domain_types request.domain_type)
                      (Datatypes.dictionary_name types typ))
              then previous
              else previous @ [ { domain_types = types; domain_type = typ } ])
        in
        { state with tables = { state.tables with function_instances; dictionaries } })

  let note_domain types typ =
    let* () = note_families types [ typ ] in
    match Datatypes.constraint_name types typ with
    | None -> return ()
    | Some name when String.equal name Prelude.in_range -> return ()
    | Some name ->
        modify (fun s ->
            if
              List.exists s.tables.domains ~f:(fun request ->
                  Option.equal String.equal
                    (Datatypes.constraint_name request.domain_types request.domain_type)
                    (Some name))
            then s
            else
              {
                s with
                tables =
                  {
                    s.tables with
                    domains =
                      s.tables.domains @ [ { domain_types = types; domain_type = typ } ];
                  };
              })

  (** A name for [base] not used yet. *)
  let fresh base s =
    let name = Fresh_names.unused s.names.used base in
    (Ok name, { s with names = { s.names with used = Set.add s.names.used name } })

  (** [f] on each of [xs] in turn: their results. *)
  let all xs ~f =
    let rec go acc = function
      | [] -> return (List.rev acc)
      | x :: rest ->
          let* y = f x in
          go (y :: acc) rest
    in
    go [] xs

  let iter xs ~f =
    let+ (_ : unit list) = all xs ~f in
    ()

  let rec fold xs ~init ~f =
    match xs with
    | [] -> return init
    | x :: rest ->
        let* acc = f init x in
        fold rest ~init:acc ~f

  let empty_path =
    { opened = []; unfolded = []; snapshots = []; positions = []; au = None }

  let empty_carried =
    {
      ghost_returns = [];
      proof_state = None;
      outline_exports = [];
      return_covered = false;
      fields_of = [];
      formals = [];
      facts = [];
      invariants = [];
      au_results = None;
      exit = None;
      handlers = [];
      pending = [];
      caught = [];
    }

  let empty_names = { used = Set.empty (module String); bound = []; scope = [] }

  (** The state of a translation before it starts. *)
  let initial =
    {
      path = empty_path;
      carried = empty_carried;
      names = empty_names;
      tables =
        {
          primitives = [];
          domains = [];
          dictionaries = [];
          function_instances = [];
          call_targets = [];
          defaults = [];
          dynamic_indices = false;
        };
      origins = [];
      warnings = [];
    }

  type local = { local_path : path; local_carried : carried; local_names : names }
  (** The state of one procedure or declaration of its own, apart from the tables and
      checks, which carry on. *)

  let new_local =
    { local_path = empty_path; local_carried = empty_carried; local_names = empty_names }

  (** Runs [m] from the state [local] of its procedure or declaration, the tables and
      checks carrying on: [m]'s result, with the state of its own that it ends in. *)
  let within local m s =
    let r, after =
      m
        {
          s with
          path = local.local_path;
          carried = local.local_carried;
          names = local.local_names;
        }
    in
    let s =
      { s with tables = after.tables; origins = after.origins; warnings = after.warnings }
    in
    match r with
    | Ok a ->
        ( Ok
            ( a,
              {
                local_path = after.path;
                local_carried = after.carried;
                local_names = after.names;
              } ),
          s )
    | Error e -> (Error e, s)

  (** Runs [m] as the translation of one procedure or declaration, from no state of its
      own. *)
  let in_procedure m = map (within new_local m) ~f:fst

  (** [m]'s result from the state [s], with the state it ends in. *)
  let run_from s m = match m s with Ok a, s -> Ok (a, s) | Error e, _ -> Error e

  (** The atomic operations used in [namespace]. *)
  let primitives_in tables namespace =
    Option.value
      (List.Assoc.find tables.primitives namespace ~equal:(List.equal String.equal))
      ~default:[]

  (** Runs [m] from the path [start], the rest of the state carrying on: its result, with
      the path it ends in, which the state then has. *)
  let arm start m s =
    match m { s with path = start } with
    | Ok a, s -> (Ok (a, s.path), s)
    | Error e, s -> (Error e, s)

  let modify_carried f = modify (fun s -> { s with carried = f s.carried })

  (** The Raven name of the OCaml variable [id] among [names], if it is bound. *)
  let name_in (names : names) (id : Ident.t) =
    List.Assoc.find names.bound (Ident.unique_name id) ~equal:String.equal

  let find_name id = gets (fun s -> name_in s.names id)

  (** The Raven name of the OCaml variable [id] of type [typ], bound now. *)
  let bind_name ?typ (id : Ident.t) s =
    let name = Fresh_names.unused s.names.used (Ident.name id) in
    ( Ok name,
      {
        s with
        names =
          {
            used = Set.add s.names.used name;
            bound = (Ident.unique_name id, name) :: s.names.bound;
            scope = (Ident.name id, (name, typ)) :: s.names.scope;
          };
      } )

  (** The variables bound so far, by their OCaml names, latest first, with their Raven
      names and types. *)
  let get_scope = gets (fun s -> s.names.scope)

  let set_scope scope = modify (fun s -> { s with names = { s.names with scope } })
end

type au = {
  self : string;  (** The procedure's name. *)
  role : Ident.t;
      (** The function that the update is of: [self], or the one it continues. *)
  ghost_results : R.Expr.t list;
      (** The ghost results witnessing facts about earlier states, which the update
          commits with. *)
  has_result : bool;
  open_ :
    contents:Types.type_expr option ->
    at:Location.t ->
    unfold:bool ->
    (R.Stmt.t list * R.Expr.t list) State_monad.t;
      (** Opens the atomic update for the step at [at], on atomics with contents of type
          [contents] if known: the statements, unfolding the atomic precondition's
          predicates and the invariants if [unfold], and the values of the implicit
          parameters. *)
  close : au_close -> value:R.Expr.t -> outcome:au_outcome -> R.Stmt.t list State_monad.t;
      (** Closes the open update, committing with the function's result [value] and its
          [outcome]. *)
  raising : R.Type.t option;
      (** The type of the function's outcome, if it may raise: then its commits pass the
          outcome after its other results. *)
  token : R.Expr.t;  (** The update's token. *)
  commit_only : at:Location.t -> value:R.Expr.t -> R.Stmt.t list State_monad.t;
      (** Opens the update and commits it with [value] at once, at the step at [at], the
          invariants left as they are. *)
}
(** The atomic update of a function with an atomic contract, whose state is in
    {!State_monad.path} and {!State_monad.carried}. *)

type lemma_signature = {
  lemma_raven : string;
  lemma_constant : bool;
  lemma_generic : Generic_parameters.t option;
  lemma_inputs : Types.type_expr list;
  lemma_implicit_count : int;
  lemma_outputs : Types.type_expr list;
}

type procedure_signature = {
  procedure_parameters : Types.type_expr list;
  procedure_variables : (string * Types.type_expr) list;
  procedure_inputs : (string * Types.type_expr) list;
  procedure_outputs : (string * Types.type_expr) list;
  procedure_result : Types.type_expr;
  procedure_returns_value : bool;
}

let map_procedure_types signature ~f =
  let open Source_type_map.Group in
  let named (name, value) =
    let+ value = typ value in
    (name, value)
  in
  let schema =
    let+ procedure_parameters = list signature.procedure_parameters ~f:typ
    and+ procedure_variables = list signature.procedure_variables ~f:named
    and+ procedure_inputs = list signature.procedure_inputs ~f:named
    and+ procedure_outputs = list signature.procedure_outputs ~f:named
    and+ procedure_result = typ signature.procedure_result in
    {
      signature with
      procedure_parameters;
      procedure_variables;
      procedure_inputs;
      procedure_outputs;
      procedure_result;
    }
  in
  run schema ~f

type atomic_shape = {
  inputs : Types.type_expr list;
  result : Types.type_expr;
  ghost_outputs : Types.type_expr list;
  implicit : Types.type_expr list;
}

type atomic_signature = {
  au_key : string;
  au_generic : Generic_parameters.t option;
  au_owner : Path.t option;
  au_private : atomic_shape;
  au_token : Types.type_expr;
  au_source : Source.proof_au;
  au_procedure : string;
  au_inputs : Types.type_expr list;
  au_result : Types.type_expr;
  au_returns_value : bool;
  au_ghost_outputs : Types.type_expr list;
  au_implicit : Types.type_expr list;
}

let atomic_source_types (au : Source.proof_au) =
  let open Source_type_map.Group in
  let+ au_parameters = list au.au_parameters ~f:typ
  and+ au_operation_type = typ au.au_operation_type
  and+ au_token = typ au.au_token in
  { au with au_parameters; au_operation_type; au_token }

let map_atomic_source_types au ~f = Source_type_map.Group.run (atomic_source_types au) ~f

let map_atomic_types signature ~f =
  let open Source_type_map.Group in
  let shape (shape : atomic_shape) =
    let+ inputs = list shape.inputs ~f:typ
    and+ result = typ shape.result
    and+ ghost_outputs = list shape.ghost_outputs ~f:typ
    and+ implicit = list shape.implicit ~f:typ in
    { inputs; result; ghost_outputs; implicit }
  in
  let schema =
    let+ au_generic =
      option signature.au_generic ~f:(fun generic ->
          let+ parameters = list generic.Generic_parameters.parameters ~f:typ
          and+ variables = list generic.variables ~f:typ in
          { generic with parameters; variables })
    and+ au_source = atomic_source_types signature.au_source
    and+ au_private = shape signature.au_private
    and+ au_token = typ signature.au_token
    and+ au_inputs = list signature.au_inputs ~f:typ
    and+ au_result = typ signature.au_result
    and+ au_ghost_outputs = list signature.au_ghost_outputs ~f:typ
    and+ au_implicit = list signature.au_implicit ~f:typ in
    {
      signature with
      au_generic;
      au_source;
      au_private;
      au_token;
      au_inputs;
      au_result;
      au_ghost_outputs;
      au_implicit;
    }
  in
  run schema ~f

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
      (** The number of explicit parameters of each predicate with implicit ones. *)
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

(** What a part of an invariant owns: atomics with contents of a type, only ghost state,
    or resources it does not say. *)
type part_owns = Atomics of Types.type_expr | Ghost | Unknown

type part = {
  part_pred : string;  (** The predicate holding it. *)
  part_source : [ `Conjunct of int | `Pending of string ];
      (** Its conjunct of the invariant's body, by position, or its pending field. *)
  part_uses : string list;
      (** The invariant's existentials it mentions, its predicate's parameters after the
          invariant's. *)
  part_owns : part_owns;
}
(** A quantified ownership of an invariant, held in a predicate that the steps unfold only
    when they need it, keeping its instances out of the other steps' proofs. *)

type structure = {
  generic : Generic_parameters.t option;
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
  parts : part list;
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

(** The values of the existentials of [st]'s invariant in the state [opened], by name. *)
let opened_bindings st (opened : opened) =
  List.map2_exn st.fields opened.values ~f:(fun (_, raven, _, _, _) v -> (raven, v))
  @ List.filter_map st.chains ~f:(fun (field, raven) ->
      Option.map (List.Assoc.find opened.indices field ~equal:String.equal) ~f:(fun v ->
          (raven, v)))
  @ List.filter_map st.pendings ~f:(fun p ->
      Option.map (List.Assoc.find opened.indices p.pending_field ~equal:String.equal)
        ~f:(fun v -> (p.pending_on, v)))

(** The arguments of [part]'s predicate for the invariant's arguments [args] and the
    existentials' values [bindings]. *)
let part_args part ~args bindings =
  args
  @ List.map part.part_uses ~f:(fun x ->
      List.Assoc.find_exn bindings x ~equal:String.equal)

type past = { inv : string; field : string; element : S.term }
(** A fact about an earlier state of a structure, [past (mem e s.f)]: [e] was in the field
    [f], owned by index, of a state of the invariant [inv], which a snapshot of its
    history and a position in [f] witness. *)

type past_return = {
  past_invariant : string;
  past_field : string;
  past_entry : R.Expr.t list -> R.Expr.t option;
  past_inputs : Types.type_expr list;
  past_result : Types.type_expr;
  past_element : Types.type_expr;
}
(** A returned history fact and the source types used to instantiate its element. *)

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

type ghost_initializer =
  | Fixed of R.Expr.t
  | Snapshot of R.Type.t
      (** A full agreement chunk over an arbitrary value of the source view type. *)

type shared = {
  persistent : (string * Location.t) list;
      (** The invariants, by their names, with their definitions. *)
  views : (string * string) list;
      (** The views, by their names, with their ghost fields, which hold a client's view
          of the state, half in the view and half in the invariant. *)
  structures : structure list;
  member_aliases : (string * string) list;
  anchors : (string * (string * ghost_initializer) list) list;
      (** Ghost fields and their initializers by source allocation tag, independent of
          storage module aliases. View initializers are arbitrary carrier values. *)
  history : History.encoding;  (** How the histories of states are encoded. *)
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
    history = History.default;
  }

type history_elements = {
  auth : R.Expr.t -> R.Expr.t;  (** The authority over the current state [s]. *)
  frag : R.Expr.t -> R.Expr.t;  (** A fragment for the state [s]. *)
  auth_frag : R.Expr.t -> R.Expr.t -> R.Expr.t;
      (** The authority over [t], with a fragment for the state [s], before it. *)
  full : R.Expr.t -> R.Expr.t;  (** The authority over [s], with a fragment for it. *)
  initial : R.Expr.t;  (** The history as allocated, before its first state. *)
}
(** The elements of the history of a structure's states. *)

(** The elements of the history of [st]'s states, in [encoding]. *)
let history_elements ~loc:l (encoding : History.encoding) st =
  let call f args =
    R.Expr.call ~loc:l (generated_module_member ~loc:l (module_name st "history") f) args
  in
  match encoding with
  | Sets ->
      let set s =
        R.Expr.call ~loc:l
          (generated_module_member ~loc:l (module_name st "states") "set")
          [ s ]
      in
      let all s =
        set (R.Expr.call ~loc:l (qualified_name ~loc:l (member_name st "states")) [ s ])
      and one s = set (R.Expr.set ~loc:l [ s ]) in
      {
        auth = (fun s -> call "auth" [ all s ]);
        frag = (fun s -> call "frag" [ one s ]);
        auth_frag = (fun t s -> call "auth_frag" [ all t; one s ]);
        full = (fun s -> call "full" [ all s ]);
        initial = call "full" [ set (R.Expr.set ~loc:l []) ];
      }
  | Monotone ->
      {
        auth = (fun s -> call "auth" [ s ]);
        frag = (fun s -> call "frag" [ s ]);
        auth_frag = (fun t s -> call "auth_frag" [ t; s ]);
        full = (fun s -> call "full" [ s ]);
        initial = call "empty" [];
      }

(** That the snapshot [snapshot] of [st]'s history, on the structure [structure], has the
    value [e] at the position [k] of its field [field]. *)
let past_fact ~loc:l ~history st ~structure ~field ~snapshot ~k e =
  let qn m x = generated_module_member ~loc:l m x in
  let entries = R.Expr.field ~loc:l snapshot (qualified_name ~loc:l field) in
  let bin op a b = R.Expr.binary ~loc:l op a b in
  List.reduce_exn ~f:(bin And)
    [
      R.Expr.own ~loc:l [ structure; (history_elements ~loc:l history st).frag snapshot ];
      bin Leq (R.Expr.int ~loc:l 0) k;
      bin Lt k (R.Expr.call ~loc:l (qn "Seq" "length") [ entries ]);
      bin Eq (R.Expr.index ~loc:l entries k) e;
    ]

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

(** The number of [predicate]'s implicit parameters, those marked [[@implicit]]; an
    invariant has none. *)
let implicit_parameters (predicate : S.predicate) =
  let* count = implicit_parameter_count ~kind:"predicate" predicate.pred_params in
  match count with
  | Some _ when predicate.pred_persistent ->
      error predicate.pred_name.pid_loc
        "Implicit parameter annotations require an ordinary predicate"
  | Some count -> Ok count
  | None -> Ok 0

type predicate_body = {
  definition : S.term;
  inline : bool;  (** Never folded or unfolded. *)
  environment : Env.t;
  project_type : Types.type_expr -> Types.type_expr;
}

type inputs = {
  types : Datatypes.t list;
  primitive_namespace : string list;
  polymorphic_functions : Polymorphic_functions.t Path_bindings.t;
  generic_predicates : Generic_predicates.t list;
  current_polymorphic : Polymorphic_functions.t option;
  functions : string Path_bindings.t;
      (** Checked functions, indexed by their compiler paths. *)
  pasts : (string * (string * string * int) list) list;
      (** The facts about earlier states that procedures require, by their names: the
          invariant, the field, and the position of the parameter that was in it. *)
  past_returns : (string * past_return list) list;
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
  raising : (string * State_monad.raise_set) list;
      (** The procedures that may raise, by name, with what they may raise. *)
  libraries : string list Path_bindings.t;
      (** The modules of the libraries, with their names: trusted Raven modules. *)
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
  current_procedure : string option;
  manual : bool;
  access_proofs : ((int * int) * Annotation.t) list;
  return_proofs : ((int * int) * Annotation.t) list;
  initializations : ((int * int) * Annotation.t) list;
  linearizations : (int * Annotation.t) list;
      (** The annotations on atomic steps, by the offset of the end of the step they
          follow. *)
  shared : shared;
}
(** What a context is given when it is made: the same throughout its translation. *)

type context = {
  given : inputs;
  au : au option;  (** The atomic update, for a function with an atomic contract. *)
}

(** The inputs of a context outside a procedure, which has none of a procedure's tables.
*)
let declaration_inputs types ~shared ~env ~preds ~spec_funcs ~proof_support
    ?(primitive_namespace = []) ?(polymorphic_functions = Path_bindings.empty)
    ?(generic_predicates = []) ?current_polymorphic () =
  let types = Generic_assets.types proof_support.resources types in
  {
    types;
    primitive_namespace;
    polymorphic_functions;
    generic_predicates;
    current_polymorphic;
    functions = Path_bindings.empty;
    lifted = [];
    pasts = [];
    past_returns = [];
    annotations = [];
    spec_funcs;
    proof_lemmas = [];
    proof_support;
    predicate_bodies = [];
    env;
    preds;
    current_procedure = None;
    manual = false;
    access_proofs = [];
    return_proofs = [];
    procedure_signatures = [];
    raising = [];
    initializations = [];
    linearizations = [];
    shared;
    ghost_args = [];
    libraries = Path_bindings.empty;
  }

let value_spec ctx ~loc typ variable =
  Option.map
    (Datatypes.admissible ~loc ctx.given.types typ (R.Expr.var ~loc (name ~loc variable)))
    ~f:R.Spec.make

let assert_admissible ctx ~loc typ variable =
  Option.value_map (value_spec ctx ~loc typ variable) ~default:[] ~f:(fun spec ->
      [ R.Stmt.assert_ ~loc spec ])

let typ ctx ~at t = Datatypes.typ ctx.given.types ~at t

let source_type_variables (given : inputs) =
  Option.bind given.current_procedure ~f:(fun procedure ->
      List.Assoc.find given.procedure_signatures procedure ~equal:String.equal)
  |> Option.value_map ~default:[] ~f:(fun signature -> signature.procedure_variables)

(** Resolve local annotation variables through the expected value type. A name stands for
    its first variable: the procedure's, then its worker's, which precede those of the
    other workers sharing its functor. *)
let source_type ?expected (given : inputs) ~at annotation =
  let variables =
    source_type_variables given
    @ List.filter_map given.types ~f:(fun data ->
        Option.bind data.Datatypes.variable ~f:(fun variable ->
            match Types.get_desc variable with
            | Tvar (Some name) -> Some (name, variable)
            | _ -> None))
    |> List.stable_dedup ~compare:(fun (left, _) (right, _) -> String.compare left right)
  in
  match (Source.ocaml_type ~variables given.env ~at annotation, expected) with
  | Ok typ, _ -> Ok typ
  | Error error, None -> Error error
  | Error _, Some expected ->
      let id = S.mk_id ~loc:at "caravan$annotated_value" in
      let value = S.mk_term (Tvar (Qid id)) at in
      let term = S.mk_term (Tcast (value, annotation)) at in
      let* () =
        Source.check_logical_expression ~type_variables:variables given.env ~functions:[]
          ~variables:[ (id.pid_str, expected) ]
          ~expected term
      in
      Ok expected

(** The explicit state, with the operations that use a context's inputs. *)
module State = struct
  include State_monad

  let typ ctx ~at source =
    let open Syntax in
    let* () = note_families ctx.given.types [ source ] in
    of_result (typ ctx ~at source)

  (** Records a check the translation generates. *)
  let record_origin origin = modify (fun s -> { s with origins = origin :: s.origins })

  open Syntax

  let note_call (given : inputs) target =
    let request = (given.primitive_namespace, target) in
    modify (fun state ->
        if List.mem state.tables.call_targets request ~equal:Poly.equal then state
        else
          {
            state with
            tables =
              { state.tables with call_targets = request :: state.tables.call_targets };
          })

  let value_instance_given (given : inputs) ~at ~target ~arguments =
    let* () = note_families given.types arguments in
    let* dictionaries =
      all arguments ~f:(fun argument ->
          match Datatypes.dictionary_name given.types argument with
          | None -> of_result (unsupported at "This polymorphic type argument")
          | Some dictionary ->
              let* () =
                modify (fun state ->
                    if
                      List.exists state.tables.dictionaries ~f:(fun request ->
                          Option.equal String.equal
                            (Datatypes.dictionary_name request.domain_types
                               request.domain_type)
                            (Some dictionary))
                    then state
                    else
                      {
                        state with
                        tables =
                          {
                            state.tables with
                            dictionaries =
                              state.tables.dictionaries
                              @ [ { domain_types = given.types; domain_type = argument } ];
                          };
                      })
              in
              return dictionary)
    in
    let namespace = given.primitive_namespace in
    let self = String.concat ~sep:"." namespace in
    let self_arguments =
      List.mapi arguments ~f:(fun index _ -> self ^ ".A" ^ Int.to_string index)
    in
    if String.equal target self then
      if List.equal String.equal dictionaries self_arguments then return self
      else of_result (unsupported at "A nonregular cyclic generic family")
    else
      let* instances = gets (fun state -> state.tables.function_instances) in
      let* instance =
        match
          List.find instances ~f:(fun instance ->
              List.equal String.equal namespace instance.instance_namespace
              && String.equal target instance.instance_worker
              && List.equal String.equal dictionaries instance.instance_arguments)
        with
        | Some instance -> return instance.instance_name
        | None ->
            let base = "Poly$Instance$" ^ Int.to_string (List.length instances) in
            let* instance_name = fresh base in
            let instance =
              {
                instance_namespace = namespace;
                instance_name;
                instance_worker = target;
                instance_arguments = dictionaries;
              }
            in
            let* () =
              modify (fun state ->
                  {
                    state with
                    tables =
                      {
                        state.tables with
                        function_instances =
                          state.tables.function_instances @ [ instance ];
                      };
                  })
            in
            return instance_name
      in
      return (String.concat ~sep:"." (namespace @ [ instance ]))

  let value_instance ctx ~at ~target ~arguments =
    value_instance_given ctx.given ~at ~target ~arguments

  let polymorphic_application ctx ~at ~path ~declaration ~occurrence ~target =
    match Path_bindings.find ctx.given.polymorphic_functions path with
    | None -> return (target, None)
    | Some worker ->
        let* arguments =
          of_result
            (Polymorphic_functions.instantiate_worker
               ~expand:(Datatypes.expand ctx.given.types)
               ~at worker ~declaration ~occurrence)
        in
        let stem = (Qualified_name.of_string target).name in
        let recursive =
          Option.exists ctx.given.current_polymorphic ~f:(fun current ->
              String.equal current.name worker.name)
        in
        if recursive then
          let same_dictionary index formal actual =
            Polymorphic_functions.same_variable formal actual
            || Option.value_map (Datatypes.dictionary_name ctx.given.types actual)
                 ~default:false ~f:(fun dictionary ->
                   String.equal dictionary (worker.name ^ ".A" ^ Int.to_string index))
          in
          if
            List.length worker.scheme.variables = List.length arguments
            && List.for_alli (List.zip_exn worker.scheme.variables arguments)
                 ~f:(fun index (formal, actual) ->
                   same_dictionary index formal (Datatypes.expand ctx.given.types actual))
          then return (worker.name ^ "." ^ stem, Some (worker, arguments))
          else of_result (unsupported at "Polymorphic recursion")
        else
          let+ instance = value_instance ctx ~at ~target:worker.name ~arguments in
          (instance ^ "." ^ stem, Some (worker, arguments))

  let polymorphic_call ctx ~at ~path ~declaration ~occurrence ~target =
    let+ target, _ =
      polymorphic_application ctx ~at ~path ~declaration ~occurrence ~target
    in
    target

  let cell_field (given : inputs) ~at elt field =
    let+ instance =
      value_instance_given given ~at ~target:Prelude.cell_family ~arguments:[ elt ]
    in
    instance ^ "." ^ field

  (** The field of reference cells with contents of type [elt]. *)
  let ref_field given ~at elt = cell_field given ~at elt "ref_contents"

  (** The field of atomics with contents of type [elt]. *)
  let atomic_field given ~at elt = cell_field given ~at elt "atomic"

  let add_primitive ~namespace ~key ~base proc =
    let* declared = gets (fun s -> primitives_in s.tables namespace) in
    match List.find declared ~f:(fun primitive -> Poly.equal primitive.key key) with
    | Some primitive -> return primitive.name
    | None ->
        let used = Set.of_list (module String) (List.map declared ~f:(fun p -> p.name)) in
        let name = Fresh_names.unused used base in
        let declaration_name = (Qualified_name.of_string name).name in
        let primitive = { key; name; member = proc declaration_name } in
        let+ () =
          modify (fun s ->
              {
                s with
                tables =
                  {
                    s.tables with
                    primitives =
                      List.Assoc.add s.tables.primitives namespace
                        (declared @ [ primitive ]) ~equal:(List.equal String.equal);
                  };
              })
        in
        name

  let primitive_key given ~at ~field elt operation =
    match Datatypes.type_key given.types elt with
    | None -> of_result (unsupported at "This primitive's payload type")
    | Some payload ->
        return
          {
            field;
            payload;
            operation;
            exact = Datatypes.immediate given.types elt;
            bounded = Datatypes.is_int given.types elt;
            admissibility = Datatypes.constraint_name given.types elt;
          }

  (** The field's name, as the stem of its primitives' names; [add_primitive] makes them
      distinct. *)
  let primitive_stem field = String.uncapitalize (Qualified_name.of_string field).name

  (** The procedure performing [op] on the atomics with contents of type [elt]. *)
  let primitive (given : inputs) ~at elt op =
    let* () = note_domain given.types elt in
    let* field = atomic_field given ~at elt in
    let* key = primitive_key given ~at ~field elt (Atomic op) in
    let declaration_name = Primitives.name ~field:(primitive_stem field) op in
    let base =
      String.concat ~sep:"." (given.primitive_namespace @ [ declaration_name ])
    in
    let* typ = of_result (Datatypes.typ given.types ~at elt) in
    add_primitive ~namespace:given.primitive_namespace ~key ~base (fun declaration_name ->
        Primitives.proc ~declaration_name ~field ~typ ~exact:key.exact ~int:key.bounded
          ?admissibility:key.admissibility op)

  (** The ordinary read or write of a mutable field. *)
  let ordinary_primitive (given : inputs) ~at ~field elt op =
    let* () = note_domain given.types elt in
    let* key = primitive_key given ~at ~field elt (Ordinary op) in
    let declaration_name = Primitives.ordinary_name ~field:(primitive_stem field) op in
    let base =
      String.concat ~sep:"." (given.primitive_namespace @ [ declaration_name ])
    in
    let* typ = of_result (Datatypes.typ given.types ~at elt) in
    add_primitive ~namespace:given.primitive_namespace ~key ~base (fun declaration_name ->
        Primitives.ordinary_proc ~declaration_name ~field ~typ ~int:key.bounded
          ?admissibility:key.admissibility op)

  (** The assertion [c] checking, at [at], what [message] says may fail. *)
  let check ~(at : Location.t) message c =
    let+ () = record_origin { at; code = Assertion; message; related = [] } in
    R.Stmt.assert_ ~loc:(loc at) (R.Spec.make c)

  (** The check that the value [v] of an [int] operation, at [at], does not overflow. *)
  let no_overflow ~at what v =
    let l = loc at in
    let bound op n = R.Expr.binary ~loc:l op v (R.Expr.int ~loc:l n) in
    check ~at
      (Printf.sprintf "This %s may overflow" what)
      (R.Expr.binary ~loc:l And (bound Geq Prelude.min_int) (bound Leq Prelude.max_int))

  (** The Raven field named [label] of the values of type [t] that are references; an
      atomic's contents have the empty label, as in [own a v]. *)
  let field_of_type (given : inputs) ~at (t : Types.type_expr) label =
    match Datatypes.desc given.types t with
    | Tconstr (p, [ elt ], _) when Datatypes.is_ref p && String.equal label "contents" ->
        let+ field = ref_field given ~at elt in
        Some field
    | Tconstr (p, [ elt ], _) when Datatypes.is_atomic p && String.is_empty label ->
        let+ field = atomic_field given ~at elt in
        Some field
    | Tconstr (p, [], _) ->
        begin match Datatypes.find given.types p with
        | Some { heap = Some fields; _ } ->
            return
              (Option.map
                 (List.find fields ~f:(fun f -> String.equal f.label label))
                 ~f:(fun f -> f.raven_field))
        | _ -> return None
        end
    | _ -> return None

  (** The Raven field of the record field [label], and whether its record is a reference;
      [None] if it is unknown. *)
  let field_of_label (given : inputs) ~at (label : Data_types.label_description) =
    match Types.get_desc label.lbl_res with
    | Tconstr (p, [ elt ], _) when Datatypes.is_ref p ->
        let+ field = ref_field given ~at elt in
        Some (field, true)
    | _ ->
        begin match Datatypes.find_label given.types label with
        | Some { heap = Some fields; _ } ->
            let field =
              List.find_exn fields ~f:(fun f -> String.equal f.label label.lbl_name)
            in
            return (Some (field.raven_field, true))
        | Some _ -> return (Some (label.lbl_name, false))
        | None -> return None
        end

  let ordinary_read ?guard (given : inputs) ~at ~field ~elt r =
    let l = loc at in
    let* proc = ordinary_primitive given ~at ~field elt Primitives.Read in
    let* typ = of_result (Datatypes.typ given.types ~at elt) in
    let+ x = fresh "tmp" in
    let value = R.Expr.var ~loc:l (name ~loc:l x) in
    let rhs = R.Stmt.expr_rhs (R.Expr.call ~loc:l (qualified_name ~loc:l proc) [ r ]) in
    let access =
      match guard with
      | None -> R.Stmt.local ~loc:l ~typ ~init:rhs (ident ~loc:l x)
      | Some condition ->
          R.Stmt.local ~loc:l ~typ (ident ~loc:l x)
          @ [ R.Stmt.if_ ~loc:l condition [ R.Stmt.assign ~loc:l [ value ] rhs ] [] ]
    in
    (access, value)

  let ordinary_write (given : inputs) ~at ~field ~elt r v =
    let l = loc at in
    let+ proc = ordinary_primitive given ~at ~field elt Primitives.Write in
    R.Stmt.call ~loc:l (R.Expr.call ~loc:l (qualified_name ~loc:l proc) [ r; v ])
end

(** The atomic that the field [label] of a value of the immutable record type [t] holds:
    its type, if it is one. *)
let atomic_in_record ctx (t : Types.type_expr) label =
  match Datatypes.instantiated ctx.given.types t with
  | Some { heap = None; ctors = [ { ocaml = ""; fields; args; _ } ]; _ } ->
      List.find_map (List.zip_exn fields args) ~f:(fun (f, a) ->
          match Datatypes.desc ctx.given.types a with
          | Tconstr (q, [ _ ], _) when String.equal f label && Datatypes.is_atomic q ->
              Some a
          | _ -> None)
  | Some _ | None -> None

(** The OCaml type of the field [label] of values of type [t] that are references, or of
    the contents of an atomic an immutable record holds. *)
let backend_field_type ctx (t : Types.type_expr) label =
  match atomic_in_record ctx t label with
  | Some atomic ->
      begin match Datatypes.desc ctx.given.types atomic with
      | Tconstr (_, [ elt ], _) -> Some elt
      | _ -> None
      end
  | None -> (
      match Datatypes.desc ctx.given.types t with
      | Tconstr (p, [ elt ], _) when Datatypes.is_ref p && String.equal label "contents"
        ->
          Some elt
      | Tconstr (p, [ elt ], _) when Datatypes.is_atomic p && String.is_empty label ->
          Some elt
      | Tconstr _ ->
          begin match Datatypes.instantiated ctx.given.types t with
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
    match Types.get_desc (Ctype.expand_head ctx.given.env t) with
    | Tconstr (path, [ element ], _)
      when Datatypes.is_atomic path && String.is_empty label ->
        Some element
    | Tconstr (path, args, _) -> (
        let declaration = Env.find_type path ctx.given.env in
        match declaration.type_kind with
        | Type_record (fields, _) ->
            Option.map
              (List.find fields ~f:(fun field ->
                   String.equal (Ident.name field.Types.ld_id) label))
              ~f:(fun field ->
                Ctype.apply ctx.given.env declaration.type_params field.ld_type args)
        | _ -> None)
    | _ -> None
  with Stdlib.Not_found -> None

let field_type ctx t label =
  Option.map (backend_field_type ctx t label) ~f:(fun fallback ->
      match source_field_type ctx t label with
      | None -> fallback
      | Some source ->
          if Option.is_some (atomic_in_record ctx t label) then
            match Types.get_desc (Ctype.expand_head ctx.given.env source) with
            | Tconstr (path, [ element ], _) when Datatypes.is_atomic path -> element
            | _ -> fallback
          else source)

let prelude_call ~loc:l f args = R.Expr.call ~loc:l (name ~loc:l f) args

(** The write of [v] to the field [field] of the reference [r]. *)
let write ~loc:l r field v =
  R.Stmt.assign ~loc:l
    [ R.Expr.field ~loc:l r (qualified_name ~loc:l field) ]
    (R.Stmt.expr_rhs v)

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
      && (potentially_contains_refs ctx.given.types a.exp_type
         || potentially_contains_refs ctx.given.types b.exp_type)
  | _ -> false

let mathematical_type ctx (t : Types.type_expr) =
  match Datatypes.desc ctx.given.types t with
  | Tconstr (p, _, _) ->
      Option.is_some (Datatypes.collection_kind ctx.given.types p)
      || List.exists ctx.given.proof_support.mathematical_types ~f:(fun d ->
          Datatypes.declares d p)
  | _ -> false

let spec_contains_runtime_refs ctx ty =
  let rec go seen ty =
    if mathematical_type ctx ty then false
    else
      match Datatypes.desc ctx.given.types ty with
      | Tvar _ | Tunivar _ -> true
      | Tconstr (p, [ _ ], _) when Datatypes.is_ref p || Datatypes.is_atomic p -> true
      | Tconstr (p, [], _) when Datatypes.is_ghost p -> true
      | Tconstr (p, args, _) ->
          List.exists args ~f:(go seen)
          || begin match Datatypes.find ctx.given.types p with
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
      (** The state of an invariant, or a record, by the values and types of its fields.
      *)

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
  Option.bind (Source.value_path env.ctx.given.env q) ~f:(fun path ->
      Path_bindings.find env.ctx.given.proof_support.runtime_functions path)

let atomic_method env = function
  | S.Qdot (parent, method_) ->
      Option.bind (Source.module_path env.ctx.given.env parent) ~f:(fun path ->
          let path = env.ctx.given.proof_support.canonical_path path in
          Option.map
            (List.find env.ctx.given.proof_support.atomic_updates ~f:(fun signature ->
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
  match
    Option.first_some atomic_key
      (env.ctx.given.proof_support.proof_key env.ctx.given.env q)
  with
  | Some key -> key
  | None ->
      begin match q with
      | S.Qid _ -> qualid_key q
      | Qdot (parent, id) ->
          let view =
            Option.bind (Source.module_path env.ctx.given.env parent) ~f:(fun path ->
                Path_bindings.find env.ctx.given.proof_support.predicate_views
                  (Path.Pdot (path, id.pid_str)))
          in
          begin match view with
          | Some key -> key
          | None ->
              begin match
                Option.bind
                  (Source.module_path env.ctx.given.env parent)
                  ~f:(Path_bindings.find env.ctx.given.proof_support.library_paths)
              with
              | None -> qualid_key q
              | Some path ->
                  Qualified_name.to_string Qualified_name.{ path; name = id.pid_str }
              end
          end
      end

let occurrence_constructor types occurrence
    (description : Data_types.constructor_description) =
  Option.bind (Datatypes.find_cstr types description) ~f:(fun (data, constructor) ->
      let data = Option.value (Datatypes.instantiated types occurrence) ~default:data in
      match (Types.get_desc description.cstr_res, Datatypes.desc types occurrence) with
      | Tconstr (_, parameters, _), Tconstr (_, arguments, _) ->
          Option.map
            (Option.all
               (List.map description.cstr_args
                  ~f:(Datatypes.instantiate_alias parameters arguments)))
            ~f:(fun args -> (data, { constructor with args }))
      | _ -> None)

let find_constructor ?occurrence env q =
  Option.bind (Source.constructor env.ctx.given.env q) ~f:(fun description ->
      match occurrence with
      | Some occurrence -> occurrence_constructor env.data occurrence description
      | None -> Datatypes.find_cstr env.data description)

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
          if signature.au_returns_value then outputs else List.drop outputs 1
        in
        [ token; inputs; R.Expr.tuple ~loc:l outputs ]
      else [ token; inputs ]

let resource_module env parent =
  Option.bind (Source.module_path env.ctx.given.env parent) ~f:(fun path ->
      let path = env.ctx.given.proof_support.canonical_path path in
      List.find env.ctx.given.proof_support.resources ~f:(fun resource ->
          Source.resource_has_path resource path))

let resource_operation env = function
  | S.Qdot (parent, operation) ->
      Option.bind (resource_module env parent) ~f:(fun resource ->
          List.find_map resource.resource_operations ~f:(fun (name, inputs, result) ->
              let generic =
                Generic_assets.operation_worker resource ~name ~inputs ~result
              in
              let target =
                Option.value_map generic
                  ~default:(resource.resource_backend ^ "." ^ name)
                  ~f:(fun worker ->
                    worker.Generic_parameters.name ^ "."
                    ^ Generic_parameters.member worker)
              in
              Option.some_if
                (String.equal name operation.pid_str)
                {
                  lemma_raven = target;
                  lemma_constant =
                    List.mem resource.resource_constants name ~equal:String.equal;
                  lemma_generic = generic;
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
          List.Assoc.find env.ctx.given.proof_support.logical_functions
            (logical_key env q) ~equal:String.equal
      end

let ghost_descriptor env q =
  Option.bind (Source.value_path env.ctx.given.env q) ~f:(fun path ->
      let path = env.ctx.given.proof_support.canonical_path path in
      List.find env.ctx.given.proof_support.ghost_fields ~f:(fun field ->
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
      List.exists env.ctx.given.proof_support.resources ~f:(fun resource ->
          resource.resource_is_ra && Source.resource_has_path resource owner))
  || List.exists env.ctx.given.proof_support.resources ~f:(fun resource ->
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
let pat_names = S.pat_names

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
  | Trecord (base, fields) -> List.concat_map (S.record_terms base fields) ~f:term_names
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
  | Trecord (base, fields) -> List.concat_map (S.record_terms base fields) ~f:refs
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
            (List.Assoc.mem env.ctx.given.preds key ~equal:String.equal
            || List.Assoc.mem env.ctx.given.proof_support.logical_functions key
                 ~equal:String.equal
            || List.Assoc.mem env.ctx.given.proof_lemmas key ~equal:String.equal)
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
    Spec_arguments.predicate_parameters ~expand:(Datatypes.expand env.data) ~bound:[]
      terms ~lookup:(fun q arguments ->
        let key = logical_key env q in
        let original = List.Assoc.find env.ctx.given.preds key ~equal:String.equal in
        match original with
        | None -> None
        | Some (target, parameters) -> (
            match
              Generic_predicates.find ~target env.ctx.given.generic_predicates key
            with
            | None -> Some parameters
            | Some predicate -> (
                let actuals =
                  List.map arguments ~f:(fun argument ->
                      match argument.S.term_desc with
                      | Tvar (Qid id) ->
                          List.Assoc.find env.var_types id.pid_str ~equal:String.equal
                      | _ ->
                          Result.ok
                            (Source.infer_logical_expression
                               ~type_variables:(source_type_variables env.ctx.given)
                               env.ctx.given.env ~functions:(List.map env.funcs ~f:fst)
                               ~variables:env.var_types argument))
                in
                match
                  let* predicate =
                    Generic_parameters.rebind ~expand:(Datatypes.expand env.data) ~at
                      predicate parameters
                  in
                  let* actuals =
                    Generic_predicates.instantiate ~environment:env.ctx.given.env
                      ~expand:(Datatypes.expand env.data) ~at predicate actuals
                  in
                  Ok (Generic_predicates.parameter_types predicate actuals)
                with
                | Ok parameters -> Some parameters
                | Error _ -> None)))
    |> List.map ~f:(fun (id, typ) -> (id.S.pid_str, typ))
  in
  let owned = List.concat_map terms ~f:owned @ passed in
  let open State.Syntax in
  let+ typed =
    State.all free ~f:(fun x ->
        match List.Assoc.find owned x ~equal:String.equal with
        | None when lenient -> State.return None
        | None ->
            State.of_result
              (error (name_loc terms x ~default:at) (Printf.sprintf "Unbound name %s" x))
        | Some t ->
            let l = loc at in
            let* typ = State.typ env.ctx ~at t in
            let+ raven = State.fresh x in
            Some (x, raven, t, typ, l))
  in
  List.filter_opt typed

(** The fields of the state [x], if [x] is one. *)
let state_fields env x =
  match List.Assoc.find env.vars x ~equal:String.equal with
  | Some (State fields) -> Some fields
  | _ -> None

(** The existential for the field [label] of the existential record [x]. *)
let existential_field x label = x ^ "_" ^ label

(** The data type and constructor of the logical record type [t], a record type without
    mutable fields, with its fields and their types. *)
let logical_record env (t : Types.type_expr) =
  Option.bind (Datatypes.instantiated env.data t) ~f:(fun d ->
      match d.ctors with
      | [ c ] when String.is_empty c.ocaml && Option.is_none d.heap ->
          Some (d, c, List.zip_exn c.fields c.args)
      | _ -> None)

(** Whether a local module has a hidden representation in this lexical environment. *)
let opaque_module_path env path =
  match path with
  | Path.Pdot _ ->
      Option.exists (Datatypes.find env.ctx.given.types path) ~f:(fun data ->
          (Option.is_some data.id
          || List.mem env.ctx.given.proof_support.public_types path ~equal:Path.same)
          &&
            try
              let declaration = Env.find_type path env.ctx.given.env in
              (match declaration.type_kind with
                | Types.Type_abstract _ -> true
                | _ -> false)
              && Option.is_none declaration.type_manifest
              || Poly.equal declaration.type_private Asttypes.Private
            with Stdlib.Not_found -> false)
  | Pident _ | Papply _ | Pextra_ty _ -> false

let opaque_module_types env =
  env.ctx.given.proof_support.strict_source_types
  || List.exists env.ctx.given.types ~f:(fun data ->
      List.exists data.Datatypes.paths ~f:(opaque_module_path env))

(** The name of a function's outcome in the terms of its contract. *)
let outcome_name = "caravan$raised"

(** The OCaml type of a function's outcome: the exception it raised, if any. *)
let outcome_type = Predef.type_option Predef.type_exn

(** The outcome of raising nothing, or the exception [e], of the Raven type [typ]. *)
let no_exception ~loc typ =
  R.Expr.annotated
    (R.Expr.call ~loc
       (Datatypes.ctor_name ~loc Datatypes.option (List.hd_exn Datatypes.option.ctors))
       [])
    typ

let raised_exception ~loc typ e =
  R.Expr.annotated
    (R.Expr.call ~loc
       (Datatypes.ctor_name ~loc Datatypes.option (List.last_exn Datatypes.option.ctors))
       [ e ])
    typ

let raise_set_names = function
  | State.Raises names -> String.concat ~sep:", " names
  | Raises_any -> "any exception"

let union_raises left right =
  match (left, right) with
  | State.Raises_any, _ | _, State.Raises_any -> State.Raises_any
  | Raises a, Raises b -> Raises (List.dedup_and_sort (a @ b) ~compare:String.compare)

(** [set] without the exceptions [handled] names, or none if [catch_all]. *)
let unhandled set ~handled ~catch_all =
  match set with
  | _ when catch_all -> State.Raises []
  | State.Raises_any -> Raises_any
  | Raises names ->
      Raises
        (List.filter names ~f:(fun n -> not (List.mem handled n ~equal:String.equal)))

(** A point after which an exception may be pending for the innermost handler. *)
let pending_point ~loc =
  let open State.Syntax in
  let point = R.Stmt.ghost_block ~loc [] in
  let+ () = State.modify_carried (fun c -> { c with pending = point :: c.pending }) in
  point

(** The statements leaving the scope at [at] with the outcome [outcome], of the Raven type
    [typ], an exception of [set], if [certain], or else if [outcome] is one: in a
    handler's protected part, recording it for the handler and marking the point; in the
    function, returning its values as they are, if its contract allows [set]. *)
let propagate ~(at : Location.t) ~certain ~typ outcome set =
  let open State.Syntax in
  let l = loc at in
  let* (carried : State.carried) = State.gets (fun (s : State.state) -> s.carried) in
  match carried.handlers with
  | handler :: outer ->
      let* () =
        State.modify_carried (fun c ->
            {
              c with
              handlers =
                { handler with reaching = union_raises handler.reaching set } :: outer;
            })
      in
      let+ point = pending_point ~loc:l in
      [ R.Stmt.assign ~loc:l [ handler.outcome ] (R.Stmt.expr_rhs outcome); point ]
  | [] -> (
      let undeclared () =
        State.of_result
          (error at
             (Printf.sprintf
                "This may raise %s, which the contract of the function does not declare: \
                 add a raises clause"
                (raise_set_names set)))
      in
      match carried.exit with
      | None -> undeclared ()
      | Some exit ->
          let allowed =
            match (exit.allowed, set) with
            | Raises_any, _ -> true
            | Raises _, Raises_any -> false
            | Raises allowed, Raises raised ->
                List.for_all raised ~f:(List.mem allowed ~equal:String.equal)
          in
          if not allowed then undeclared ()
          else
            let leave = [ R.Stmt.return ~loc:l (exit.results @ [ outcome ]) ] in
            State.return
              (if certain then leave
               else
                 [
                   R.Stmt.if_ ~loc:l
                     (R.Expr.binary ~loc:l Neq outcome (no_exception ~loc:l typ))
                     leave [];
                 ]))

(** [stmts] with the statements after each pending point guarded by the innermost
    handler's outcome being none, so that they do not run once an exception is pending. *)
let nest stmts =
  let open State.Syntax in
  let+ (carried : State.carried) = State.gets (fun (s : State.state) -> s.carried) in
  match carried.handlers with
  | [] -> stmts
  | handler :: _ ->
      let pending stmt = List.exists carried.pending ~f:(phys_equal stmt) in
      List.fold_right stmts ~init:[] ~f:(fun stmt rest ->
          if pending stmt then
            match rest with
            | [] -> []
            | _ ->
                let loc = R.Loc.none in
                [
                  R.Stmt.if_ ~loc
                    (R.Expr.binary ~loc Eq handler.outcome
                       (no_exception ~loc handler.outcome_type))
                    rest [];
                ]
          else stmt :: rest)

(** The number of pending points so far, to tell whether a branch's arms have one. *)
let pending_count = State.gets (fun (s : State.state) -> List.length s.carried.pending)

(** A pending point after a branch whose arms marked one since [before] points. *)
let after_branch ~loc before =
  let open State.Syntax in
  let* (carried : State.carried) = State.gets (fun (s : State.state) -> s.carried) in
  if List.is_empty carried.handlers || List.length carried.pending = before then
    State.return []
  else
    let+ point = pending_point ~loc in
    [ point ]

(** An arbitrary carrier value, without a source admissibility assumption. *)
let raw_default ctx ~at typ =
  let open State.Syntax in
  let* carrier = State.of_result (Datatypes.typ ctx.given.types ~at typ) in
  let* key =
    match Datatypes.type_key ctx.given.types typ with
    | Some key -> State.return key
    | None -> State.of_result (unsupported at "An unreachable expression of this type")
  in
  let namespace = ctx.given.primitive_namespace in
  let stem = "ocaml_default$" ^ Datatypes.key_name key in
  let qualified = String.concat ~sep:"." (namespace @ [ stem ]) in
  let+ () =
    State.modify (fun (s : State.state) ->
        if
          List.exists s.tables.defaults ~f:(fun request ->
              String.equal request.default_name qualified)
        then s
        else
          {
            s with
            tables =
              {
                s.tables with
                defaults =
                  s.tables.defaults
                  @ [
                      {
                        default_namespace = namespace;
                        default_name = qualified;
                        default_type = carrier;
                      };
                    ];
              };
          })
  in
  R.Expr.var ~loc:(loc at) (qualified_name ~loc:(loc at) qualified)
