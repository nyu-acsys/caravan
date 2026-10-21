(** The translation of OCaml implementations to Raven programs.

    So far: top-level functions on integers, booleans, unit, tuples and variant types,
    with their contracts. A function becomes a procedure, and a variant type a data type
    (see {!Datatypes}). Expressions are put in A-normal form, since a call is a statement
    in Raven; arguments are evaluated right to left, as OCaml does. *)

open Base
module R = Raven_api

type error = Report.error

let ( let* ) = Result.( >>= )
let error loc message = Error (Report.error Type loc message)
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

type origin = { at : Location.t; message : string }
(** A check the translation generates, with what it checks, as the message to report when
    it fails. *)

(** Whether a function with an atomic contract has linearized, as far as the translation
    knows: committed its atomic update, or not yet; or committed if the last
    [compare_and_set] succeeded. *)
type au_state = Pending | Committed | Unknown | On_cas

(** What a function with an atomic contract does at an atomic step on its abstract state.
*)
type au_close =
  | Commit  (** The step linearizes the function. *)
  | Abort  (** The step does not change the abstract state. *)
  | Commit_call  (** The step is a call, which linearizes the function in its place. *)

type au = {
  mutable state : au_state;
  mutable cas_results : (string * bool) list;
      (** Variables bound to the result of a [compare_and_set], or its negation if
          [false], by their unique names. *)
  self : string;  (** The procedure's name. *)
  open_ :
    at:Location.t -> unfold:bool -> (R.Stmt.t list * R.Expr.t list, Report.error) Result.t;
      (** Opens the atomic update for the step at [at]: the statements, unfolding the
          atomic precondition's predicates if [unfold], and the values of the implicit
          parameters. *)
  close :
    at:Location.t -> au_close -> R.Expr.t list -> (R.Stmt.t list, Report.error) Result.t;
      (** Closes the atomic update opened with the values of the implicit parameters. *)
}
(** The atomic update of a function with an atomic contract. *)

type context = {
  types : Datatypes.t list;
  refs : (string * R.Type.t) list ref;
      (** The fields of the ref cells and atomics used so far, by their names, with their
          types. *)
  primitives : (string * R.Member.t) list ref;
      (** The atomic operations used so far, by their names (see {!Primitives}). *)
  names : Names.t;
  functions : (string * string) list;
      (** The top-level functions, by the unique name of their OCaml identifier. *)
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
}

let typ ctx ~at t = Datatypes.typ ctx.types ~at t

(** The field of the ref cells with contents of type [elt]. *)
let ref_field ctx ~at elt =
  let field = "ref_" ^ Datatypes.tag ctx.types elt ^ "_contents" in
  let* t = typ ctx ~at elt in
  if not (List.Assoc.mem !(ctx.refs) field ~equal:String.equal) then
    ctx.refs := !(ctx.refs) @ [ (field, t) ];
  Ok field

(** The field of the atomics with contents of type [elt]. *)
let atomic_field ctx ~at elt =
  let field = "atomic_" ^ Datatypes.tag ctx.types elt in
  let* t = typ ctx ~at elt in
  if not (List.Assoc.mem !(ctx.refs) field ~equal:String.equal) then
    ctx.refs := !(ctx.refs) @ [ (field, t) ];
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
          (name, Primitives.proc ~field ~typ ~exact:(Datatypes.immediate ctx.types elt) op);
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

(** The OCaml type of the field [label] of values of type [t] that are references. *)
let field_type ctx (t : Types.type_expr) label =
  match Datatypes.desc ctx.types t with
  | Tconstr (p, [ elt ], _) when Datatypes.is_ref p && String.equal label "contents" ->
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
  | _ -> None

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
  ctx.origins := { at; message } :: !(ctx.origins);
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

module S = Caravan_spec.Spec_ast

(** What a name in a contract stands for: a Raven variable, or a value, such as the field
    of a matched value that a pattern names. *)
type bound = Raven of string | Value of R.Expr.t

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

(** The head of the application [t] and its arguments. *)
let rec spine (t : S.term) args =
  match t.term_desc with Tapply (f, a) -> spine f (a :: args) | _ -> (t, args)

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
    || List.mem [ "own"; "not"; "max_int"; "min_int"; "mod" ] x ~equal:String.equal
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
      Ok
        (match q with
        | Tforall -> R.Expr.forall ~loc:l vars body
        | Texists -> R.Expr.exists ~loc:l vars body)
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
      let* location = location_of env location in
      let* v = formula env v in
      Ok (R.Expr.own ~loc:l [ location; v ])
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
          let* a = formula env a in
          let* b = formula env b in
          match op with
          | Div -> Ok (prelude_call ~loc:l Prelude.div [ a; b ])
          | Mod -> Ok (prelude_call ~loc:l Prelude.mod_ [ a; b ])
          | _ -> Ok (R.Expr.binary ~loc:l op a b))
      end
  | Tvar (Qid { pid_str = c; _ }), _ when is_constructor c -> constructor env t args
  | Tvar (Qid { pid_str = f; _ }), _ :: _
    when List.Assoc.mem env.funcs f ~equal:String.equal ->
      let* args = all args ~f:(formula env) in
      let func = List.Assoc.find_exn env.funcs f ~equal:String.equal in
      Ok (R.Expr.call ~loc:l (name ~loc:l func) args)
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
          match field with
          | Some field -> Ok (R.Expr.field ~loc:l r (name ~loc:l field))
          | None -> error at (Printf.sprintf "%s has no mutable field %s" x label)
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
  | _ -> unsupported at "This location, other than a field of a variable or an atomic,"

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

(** The statements of [access], an atomic step, inside the atomic update of a function
    with an atomic contract that has not linearized yet; [close] says how the step closes
    it, [`Cas x] by committing if [x], the result of a [compare_and_set], holds. *)
let linearize ctx ~at (close : [ `Close of au_close | `Cas of R.Expr.t ]) access =
  match ctx.au with
  | None -> Ok access
  | Some au ->
      begin match au.state with
      | Committed -> Ok access
      | Unknown | On_cas ->
          error at
            "Caravan cannot tell whether the function has linearized before this step"
      | Pending ->
          let* opening, values = au.open_ ~at ~unfold:true in
          let* closing =
            match close with
            | `Close c ->
                au.state <- (match c with Abort -> Pending | _ -> Committed);
                au.close ~at c values
            | `Cas x ->
                let* commit = au.close ~at Commit values in
                let* abort = au.close ~at Abort values in
                au.state <- On_cas;
                Ok [ R.Stmt.if_ ~loc:(loc at) x commit abort ]
          in
          Ok (opening @ access @ closing)
      end

(** The state of the atomic update after two branches. *)
let join_au a b = if Poly.equal a b then a else Unknown

let au_state ctx = Option.map ctx.au ~f:(fun au -> au.state)

let set_au_state ctx = function
  | Some state -> Option.iter ctx.au ~f:(fun au -> au.state <- state)
  | None -> ()

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

let no_loop_before_linearizing ctx ~at =
  match au_state ctx with
  | None | Some Committed -> Ok ()
  | Some _ ->
      unsupported at "A loop in a function with an atomic contract, before it linearizes,"

(** The statements evaluating [e], and the value of [e] after them. *)
let rec expr (ctx : context) (e : Typedtree.expression) :
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
          let init =
            R.Stmt.new_rhs
              (List.map2_exn fields args ~f:(fun f v -> (name ~loc:l f, Some v)))
          in
          Ok
            ( stmts @ R.Stmt.local ~loc:l ~typ ~init (ident ~loc:l x),
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
            ( stmts
              @ R.Stmt.local ~loc:l ~typ ~init:read (ident ~loc:l x)
              @ assume_in_range ~loc:l e.exp_type x,
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
      let* stmts =
        branch ctx e (fun target -> match_cases ctx ~at v cases ~total target)
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
        branch ctx e (fun target -> conditional ctx ~at ?polarity c e1 e2 target)
      in
      Ok (c_stmts @ fst stmts, snd stmts)
  | Texp_let (Nonrecursive, bindings, body) ->
      (* The bound expressions are evaluated before any of their variables is bound. *)
      let* evaluated =
        all bindings ~f:(fun (vb : Typedtree.value_binding) ->
            let polarity = cas_polarity ctx vb.vb_expr in
            let* stmts, v = expr ctx vb.vb_expr in
            begin match (ctx.au, polarity, vb.vb_pat.pat_desc) with
            | Some au, Some p, Tpat_var (id, _, _) ->
                au.cas_results <- (Ident.unique_name id, p) :: au.cas_results
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
      let* body_stmts, body = expr ctx body in
      Ok
        ( List.concat_map evaluated ~f:(fun (_, stmts, _) -> stmts)
          @ List.concat (List.concat defs)
          @ ghost @ body_stmts,
          body )
  | Texp_let (Recursive, _, _) -> unsupported at "A local recursive function"
  | Texp_sequence (e1, e2) ->
      let* stmts1, _ = expr ctx e1 in
      let* ghost = ghost ctx ~after:e1.exp_loc.loc_end ~before:e2.exp_loc.loc_start in
      let* stmts2, v = expr ctx e2 in
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
      ( R.Stmt.local ~loc:l ~typ ~init:rhs (ident ~loc:l x)
        @ assume_in_range ~loc:l typ_of x,
        R.Expr.var ~loc:l (name ~loc:l x) )
  in
  match (stdlib_name path, args) with
  | _ when Option.is_some (atomic_name path) ->
      atomic ctx e (Option.value_exn (atomic_name path)) args
  | Some "ref", [ v ] ->
      let* field = ref_field ctx ~at v.exp_type in
      let* stmts, v = expr ctx v in
      let x = Names.fresh ctx.names "tmp" in
      let init = R.Stmt.new_rhs [ (name ~loc:l field, Some v) ] in
      Ok
        ( stmts @ R.Stmt.local ~loc:l ~typ:(R.Type.ref ~loc:l) ~init (ident ~loc:l x),
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
  (* The result of [f] applied to the atomic and [args], in a variable, a step closing an
     atomic update as [close] says. *)
  let result ?close f atomic args =
    let* typ = typ ctx ~at e.exp_type in
    let x = Names.fresh ctx.names "tmp" in
    let v = R.Expr.var ~loc:l (name ~loc:l x) in
    let init = R.Stmt.expr_rhs (R.Expr.call ~loc:l (name ~loc:l f) (atomic :: args)) in
    let close = Option.value close ~default:(`Close Commit) in
    let* step =
      linearize ctx ~at
        (match close with `Cas -> `Cas v | `Close c -> `Close c)
        (R.Stmt.local ~loc:l ~typ ~init (ident ~loc:l x))
    in
    Ok (step @ assume_in_range ~loc:l e.exp_type x, v)
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
      let init = R.Stmt.new_rhs [ (name ~loc:l field, Some v) ] in
      Ok
        ( stmts @ R.Stmt.local ~loc:l ~typ:(R.Type.ref ~loc:l) ~init (ident ~loc:l x),
          R.Expr.var ~loc:l (name ~loc:l x) )
  | "get", [ a ] ->
      let* typ = typ ctx ~at e.exp_type in
      let x = Names.fresh ctx.names "tmp" in
      let read = R.Stmt.expr_rhs (R.Expr.field ~loc:l a (name ~loc:l field)) in
      let* step =
        linearize ctx ~at (`Close Abort)
          (R.Stmt.local ~loc:l ~typ ~init:read (ident ~loc:l x))
      in
      Ok
        ( stmts @ step @ assume_in_range ~loc:l e.exp_type x,
          R.Expr.var ~loc:l (name ~loc:l x) )
  | "set", [ a; v ] ->
      let* step = linearize ctx ~at (`Close Commit) [ write ~loc:l a field v ] in
      Ok (stmts @ step, unit_value ~loc:l)
  | "exchange", [ a; v ] ->
      let* f = primitive Exchange in
      let* reading, r = result f a [ v ] in
      Ok (stmts @ reading, r)
  | "compare_and_set", [ a; old_val; new_val ] ->
      let* f = primitive Compare_and_set in
      let* reading, r = result ~close:`Cas f a [ old_val; new_val ] in
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
      let* step =
        linearize ctx ~at (`Close Commit)
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
      let* b_stmts, b = expr ctx b in
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
  (* A recursive call before the function linearizes is a retry, which linearizes it in
     its place, with the atomic update's values of the implicit parameters. *)
  let* opening, implicit, closing =
    match ctx.au with
    | Some au when String.equal au.self f ->
        begin match au.state with
        | Pending ->
            let* opening, values = au.open_ ~at:e.exp_loc ~unfold:false in
            let* closing = au.close ~at:e.exp_loc Commit_call values in
            au.state <- Committed;
            Ok (opening, values, closing)
        | Committed -> Ok ([], [], [])
        | Unknown | On_cas ->
            error e.exp_loc
              "Caravan cannot tell whether the function has linearized before this call"
        end
    | _ -> Ok ([], [], [])
  in
  let callee = R.Expr.call ~loc:l (name ~loc:l f) (args @ implicit) in
  if is_unit e.exp_type then
    Ok (stmts @ opening @ [ R.Stmt.call ~loc:l callee ] @ closing, unit_value ~loc:l)
  else
    let* typ = typ ctx ~at:e.exp_loc e.exp_type in
    let x = Names.fresh ctx.names "tmp" in
    let def = R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs callee) (ident ~loc:l x) in
    Ok (stmts @ opening @ def @ closing, R.Expr.var ~loc:l (name ~loc:l x))

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
and match_cases ctx ~at v (cases : (Typedtree.pattern * Typedtree.expression) list) ~total
    target =
  let l = loc at in
  (* Each case starts in the state of the atomic update before the match. *)
  let start = au_state ctx in
  let ends = ref [] in
  (* The body of a case, after defining the variables of its pattern. *)
  let case_body binds (rhs : Typedtree.expression) =
    set_au_state ctx start;
    let* defs =
      all binds ~f:(fun (id, value, t) ->
          let* typ = typ ctx ~at t in
          let x = Names.bind ~typ:t ctx.names id in
          Ok
            (R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs value) (ident ~loc:l x)
            @ assume_in_range ~loc:l t x))
    in
    let* stmts, value = expr ctx rhs in
    let assignment =
      Option.value_map target ~default:[] ~f:(fun t -> [ assign t value ])
    in
    ends := au_state ctx :: !ends;
    Ok (List.concat defs @ stmts @ assignment)
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
    (Option.first_some (List.reduce (List.filter_opt !ends) ~f:join_au) start);
  Ok stmts

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
and conditional ctx ~at ?polarity c (e1 : Typedtree.expression)
    (e2 : Typedtree.expression option) target =
  let l = loc at in
  (* The state of the atomic update in each arm: if [c] is the result of the
     [compare_and_set] that may have linearized the function, whether it did. *)
  let start = au_state ctx in
  let arm_state taken =
    match (start, polarity) with
    | Some On_cas, Some p -> Some (if Bool.equal p taken then Committed else Pending)
    | _ -> start
  in
  let arm taken e =
    set_au_state ctx (arm_state taken);
    let* stmts =
      match e with
      | None -> Ok []
      | Some e -> (
          let* stmts, v = expr ctx e in
          match target with Some t -> Ok (stmts @ [ assign t v ]) | None -> Ok stmts)
    in
    Ok (stmts, au_state ctx)
  in
  let* then_, then_state = arm true (Some e1) in
  let* else_, else_state = arm false e2 in
  set_au_state ctx (Option.map2 then_state else_state ~f:join_au);
  Ok [ R.Stmt.if_ ~loc:l c then_ else_ ]

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
}
(** A top-level function [f] with its parameters [params] and [body], and its contract. *)

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
  let* implicit = implicit_vars env f in
  let env =
    List.fold implicit ~init:env ~f:(fun env (x, raven, t, _) ->
        { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
  in
  Ok (result_name, env, implicit)

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
let func types ~refs ~primitives ~ocaml_env ~preds ~funcs ~spec_funcs origins (f : func) :
    (R.Callable.t, error) Result.t =
  let ctx =
    {
      types;
      refs;
      primitives;
      names = Names.create ();
      functions = [];
      origins;
      annotations = [];
      spec_funcs;
      env = ocaml_env;
      preds;
      facts = [];
      au = None;
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

(** The predicates that the conjunction [t] applies, with their arguments, as [p x] in
    [p x && b = false]. *)
let rec predicate_apps ctx (t : S.term) =
  let t = S.chain t in
  let head, args = spine t [] in
  match (head.term_desc, args) with
  | Tvar (Qid { pid_str = "&&" | "/\\"; _ }), [ a; b ] ->
      predicate_apps ctx a @ predicate_apps ctx b
  | Tvar (Qid { pid_str = p; _ }), _ when List.Assoc.mem ctx.preds p ~equal:String.equal
    ->
      [ (p, args, t.term_loc) ]
  | _ -> []

(** The statements binding the atomic update of the function [self], whose atomic contract
    has the preconditions [pres] and postconditions [posts], and whose implicit parameters
    are [implicit]; sets [ctx.au]. An atomic step inside the update unfolds the predicates
    of [pres], and folds those of [posts] if it commits, and those of [pres] otherwise. *)
let atomic_update ctx env ~at ~self implicit ~pres ~posts =
  let fun_loc = at in
  let phi = Names.fresh ctx.names "phi" in
  let au_call ~l f args =
    R.Expr.call ~loc:l (name ~loc:l f) (R.Expr.var ~loc:l (name ~loc:l phi) :: args)
  in
  let pre_preds = List.concat_map pres ~f:(predicate_apps ctx) in
  let post_preds = List.concat_map posts ~f:(predicate_apps ctx) in
  (* The contract's environment, with the values of the implicit parameters in the
     update. *)
  let opened values =
    List.fold2_exn implicit values ~init:env ~f:(fun env (x, _, _, _) v ->
        bind env x (Value v))
  in
  let uses make env preds =
    all preds ~f:(fun (p, args, at) ->
        let raven, _ = List.Assoc.find_exn ctx.preds p ~equal:String.equal in
        let* args = all args ~f:(formula env) in
        let l = loc at in
        Ok (make ~loc:l (name ~loc:l raven) args))
  in
  let commit ~l = R.Stmt.call ~loc:l (au_call ~l "commitAU" [ unit_value ~loc:l ]) in
  let open_ ~at ~unfold =
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
    let* unfolds =
      uses
        (fun ~loc p args -> R.Stmt.unfold ~loc p args)
        (opened values)
        (if unfold then pre_preds else [])
    in
    Ok (List.concat_map decls ~f:fst @ [ opening ] @ unfolds, values)
  in
  let close ~at c values =
    let l = loc at in
    let fold preds =
      uses (fun ~loc p args -> R.Stmt.fold ~loc p args) (opened values) preds
    in
    match c with
    | Commit ->
        let* folds = fold post_preds in
        Ok (folds @ [ commit ~l ])
    | Abort ->
        let* folds = fold pre_preds in
        Ok (folds @ [ R.Stmt.call ~loc:l (au_call ~l "abortAU" []) ])
    | Commit_call -> Ok [ commit ~l ]
  in
  ctx.au <- Some { state = Pending; cas_results = []; self; open_; close };
  let l = loc fun_loc in
  Ok
    (R.Stmt.local ~loc:l ~ghost:true ~const:true
       ~init:(R.Stmt.expr_rhs (R.Expr.call ~loc:l (name ~loc:l "bindAU") []))
       (ident ~loc:l phi))

(** The procedure of [f], named [proc_name]; if [f] is pure, its result is the value of
    its function. [funcs] are the functions contracts can call, by their OCaml names. *)
let proc types ~refs ~primitives ~ocaml_env ~preds ~funcs ~annotations
    (functions : (string * string) list) origins ~proc_name ~pure (f : func) :
    (R.Callable.t, error) Result.t =
  let names = Names.create () in
  let ctx =
    {
      types;
      refs;
      primitives;
      names;
      functions;
      origins;
      annotations;
      spec_funcs = funcs;
      env = ocaml_env;
      preds;
      facts = [];
      au = None;
    }
  in
  let l = loc f.loc in
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
  let atomic = Option.exists f.contract ~f:(fun c -> c.atomic) in
  let* () =
    if atomic && not (List.is_empty returns) then
      unsupported f.loc "An atomic contract of a function with a result"
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
      atomic_update ctx env ~at:f.loc ~self:proc_name implicit_decls ~pres:atomic_pres
        ~posts:atomic_posts
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
  let requires = in_range @ requires @ atomic_requires in
  let ensures = Option.to_list result_in_range @ defined @ ensures @ atomic_ensures in
  let* first = ghost ctx ~after:f.loc.loc_start ~before:f.body.exp_loc.loc_start in
  let* stmts, v = expr ctx f.body in
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
    | Some (Unknown | On_cas) ->
        error f.loc "Caravan cannot tell whether this function linearizes on every path"
  in
  let body = bind_au @ first @ stmts @ assignment @ last in
  Ok
    (R.Callable.proc ~loc:l
       ~formals:(List.map formals ~f:(fun (_, _, v) -> v) @ implicit)
       ~returns ~requires ~ensures (ident ~loc:l proc_name) (Some body))

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

(** The data types and functions of [structure], in order, with the contracts of the
    functions in [annotations]. *)
let items (structure : Typedtree.structure) (annotations : Annotation.t list) :
    (Datatypes.t list * func list, error) Result.t =
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
                  Ok
                    {
                      id;
                      raven_name = Ident.name id;
                      params;
                      body;
                      loc = vb.vb_loc;
                      contract;
                      next;
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

(** The predicate [p], declared at [at], whose parameters have the OCaml types [types]. *)
let predicate types ~refs ~primitives ~ocaml_env ~preds ~spec_funcs origins ~at
    (p : S.predicate) param_types : (R.Callable.t, error) Result.t =
  let ctx =
    {
      types;
      refs;
      primitives;
      names = Names.create ();
      functions = [];
      origins;
      annotations = [];
      spec_funcs;
      env = ocaml_env;
      preds;
      facts = [];
      au = None;
    }
  in
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
      data = types;
      funcs = spec_funcs;
      vars = List.map params ~f:(fun (x, raven, _, _) -> (x, Raven raven));
    }
  in
  let* body = quantified env p.pred_body in
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
  let vars = List.map ~f:(fun (_, _, _, v) -> v) in
  Ok
    (R.Callable.func ~loc:l ~kind:Pred ~formals:(vars inputs) ~returns:(vars outputs)
       (ident ~loc:l p.pred_name.pid_str)
       (Some body))

(** The Raven program of [source]. *)
let program (source : Source.t) : (R.Program.t * origin list, error) Result.t =
  let annotations = Annotation.of_comments source.comments in
  let* types, funcs = items source.typed annotations in
  (* Each data type's module, given the ones declared before it; a record type that is a
     reference has fields instead. *)
  let* modules =
    all
      (List.filter_mapi types ~f:(fun i (d : Datatypes.t) ->
           Option.some_if
             (Option.is_none d.heap && Option.is_none d.alias)
             (List.take types i, d)))
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
  let origins = ref [] in
  let ocaml_env = source.env in
  (* The predicates' signatures first, for their bodies and the contracts to use. *)
  let* predicates =
    all
      (List.filter annotations ~f:(fun a ->
           Poly.equal (Annotation.kind a) Annotation.Predicate))
      ~f:(fun a ->
        let* p = Annotation.predicate a in
        let* param_types =
          all p.pred_params ~f:(fun (_, t) -> Source.ocaml_type ocaml_env ~at:a.loc t)
        in
        Ok (a, p, param_types))
  in
  let preds =
    List.map predicates ~f:(fun (_, p, types) ->
        (p.pred_name.pid_str, (p.pred_name.pid_str, types)))
  in
  let spec_funcs =
    List.map pure ~f:(fun f -> (Ident.name f.id, f.raven_name))
    @ List.map preds ~f:(fun (p, (raven, _)) -> (p, raven))
  in
  let* pred_members =
    all predicates ~f:(fun ((a : Annotation.t), p, param_types) ->
        predicate types ~refs ~primitives ~ocaml_env ~preds ~spec_funcs origins ~at:a.loc
          p param_types)
  in
  let* pure_funcs =
    all pure
      ~f:
        (func types ~refs ~primitives ~ocaml_env ~preds
           ~funcs:(List.map pure ~f:(fun f -> (Ident.unique_name f.id, f.raven_name)))
           ~spec_funcs origins)
  in
  let* procs =
    all funcs ~f:(fun f ->
        proc types ~refs ~primitives ~ocaml_env ~preds ~funcs:spec_funcs ~annotations
          functions origins ~proc_name:(proc_name f) ~pure:(is_pure f) f)
  in
  let file_start = { Lexing.dummy_pos with pos_fname = source.file } in
  let start = R.Loc.make file_start file_start in
  let ref_fields =
    List.map !refs ~f:(fun (field, t) ->
        R.Member.field ~loc:start (ident ~loc:start field) t)
  in
  Ok
    ( R.Program.make ~loc:start
        (Prelude.members @ modules @ record_fields @ ref_fields
       @ List.map !primitives ~f:snd
        @ List.map (pred_members @ pure_funcs @ procs) ~f:R.Member.callable),
      !origins )
