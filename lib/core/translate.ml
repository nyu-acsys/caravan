(** The translation of OCaml implementations to Raven programs.

    So far: top-level functions on integers, booleans and unit, with their contracts. A
    function becomes a procedure. Expressions are put in A-normal form, since a call is a
    statement in Raven; arguments are evaluated right to left, as OCaml does. *)

open Base
module R = Raven_api

type error = Report.error

let ( let* ) = Result.( >>= )
let error loc message = Error (Report.error Type loc message)

let unsupported loc what =
  Error (Report.error Unsupported loc (what ^ " is not supported yet"))

let loc (l : Location.t) = R.Loc.make l.loc_start l.loc_end
let ident ~loc name = R.Ident.make ~loc name
let name ~loc n = R.Name.make ~loc n

(** [f] mapped over [xs], stopping at the first error. *)
let all (xs : 'a list) ~(f : 'a -> ('b, error) Result.t) : ('b list, error) Result.t =
  Result.all (List.map xs ~f)

(** The Raven type of the OCaml type [t]. *)
let typ ~(at : Location.t) (t : Types.type_expr) : (R.Type.t, error) Result.t =
  let loc = loc at in
  match Types.get_desc t with
  | Tconstr (p, [], _) when Path.same p Predef.path_int -> Ok (R.Type.int ~loc)
  | Tconstr (p, [], _) when Path.same p Predef.path_bool -> Ok (R.Type.bool ~loc)
  | Tconstr (p, [], _) when Path.same p Predef.path_unit -> Ok (R.Type.tuple ~loc [])
  | _ -> unsupported at (Stdlib.Format.asprintf "The type %a" Printtyp.type_expr t)

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

(** The names of a function's variables in Raven: OCaml's, made distinct where a name is
    bound twice. *)
module Names = struct
  type t = { mutable used : Set.M(String).t; mutable bound : (string * string) list }

  let create () = { used = Set.empty (module String); bound = [] }

  (** A name for [base] not used yet. *)
  let fresh names base =
    let rec go n =
      let candidate = if n = 0 then base else Printf.sprintf "%s_%d" base n in
      if Set.mem names.used candidate then go (n + 1) else candidate
    in
    let name = go 0 in
    names.used <- Set.add names.used name;
    name

  (** The Raven name of the OCaml variable [id], bound now. *)
  let bind names (id : Ident.t) =
    let name = fresh names (Ident.name id) in
    names.bound <- (Ident.unique_name id, name) :: names.bound;
    name

  let find names (id : Ident.t) =
    List.Assoc.find names.bound (Ident.unique_name id) ~equal:String.equal
end

type origin = { at : Location.t; message : string }
(** A check the translation generates, with what it checks, as the message to report when
    it fails. *)

type context = {
  names : Names.t;
  functions : (string * string) list;
      (** The top-level functions, by the unique name of their OCaml identifier. *)
  origins : origin list ref;
}

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

(** The name of [p] if it is a value of the standard library's toplevel. *)
let stdlib_name (p : Path.t) =
  match p with
  | Pdot (Pident m, x) when String.equal (Ident.name m) "Stdlib" -> Some x
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

let unop_of_path (p : Path.t) =
  match stdlib_name p with Some "not" -> Some `Not | Some "~-" -> Some `Neg | _ -> None

let unit_value ~loc = R.Expr.tuple ~loc []

(** The arguments of an application, if all are given and unlabelled. *)
let plain_args ~at (args : (Asttypes.arg_label * Typedtree.apply_arg) list) =
  all args ~f:(function
    | Nolabel, Arg e -> Ok e
    | _ -> unsupported at "A labelled, optional or omitted argument")

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
  | Texp_construct _ -> unsupported at "This constructor"
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, args) ->
      let* args = plain_args ~at args in
      apply ctx e path args
  | Texp_apply _ -> unsupported at "This application"
  | Texp_ifthenelse (c, e1, e2) ->
      let* c_stmts, c = expr ctx c in
      let* stmts = branch ctx e (fun target -> conditional ctx ~at c e1 e2 target) in
      Ok (c_stmts @ fst stmts, snd stmts)
  | Texp_let
      ( Nonrecursive,
        [ { vb_pat = { pat_desc = Tpat_var (id, _, _); _ }; vb_expr; _ } ],
        body ) ->
      let* stmts, v = expr ctx vb_expr in
      let* typ = typ ~at:vb_expr.exp_loc vb_expr.exp_type in
      let x = Names.bind ctx.names id in
      let def =
        R.Stmt.local ~loc:l ~const:true ~typ ~init:(R.Stmt.expr_rhs v) (ident ~loc:l x)
      in
      let* body_stmts, body = expr ctx body in
      Ok (stmts @ def @ body_stmts, body)
  | Texp_let _ -> unsupported at "This let binding"
  | Texp_sequence (e1, e2) ->
      let* stmts1, _ = expr ctx e1 in
      let* stmts2, v = expr ctx e2 in
      Ok (stmts1 @ stmts2, v)
  | Texp_assert (c, _) ->
      let* stmts, c = expr ctx c in
      Ok (stmts @ [ R.Stmt.assert_ ~loc:l (R.Spec.make c) ], unit_value ~loc:l)
  | _ -> unsupported at "This expression"

(** The application of the function at [path] to [args], in [e]. *)
and apply ctx (e : Typedtree.expression) (path : Path.t)
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
  let callee = R.Expr.call ~loc:l (name ~loc:l f) args in
  if is_unit e.exp_type then Ok (stmts @ [ R.Stmt.call ~loc:l callee ], unit_value ~loc:l)
  else
    let* typ = typ ~at:e.exp_loc e.exp_type in
    let x = Names.fresh ctx.names "tmp" in
    let def = R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs callee) (ident ~loc:l x) in
    Ok (stmts @ def, R.Expr.var ~loc:l (name ~loc:l x))

(** [if c then e1 else e2], with its value assigned to [target] if there is one. *)
and conditional ctx ~at c (e1 : Typedtree.expression) (e2 : Typedtree.expression option)
    target =
  let l = loc at in
  let arm = function
    | None -> Ok []
    | Some e -> (
        let* stmts, v = expr ctx e in
        match target with Some t -> Ok (stmts @ [ assign t v ]) | None -> Ok stmts)
  in
  let* then_ = arm (Some e1) in
  let* else_ = arm e2 in
  Ok [ R.Stmt.if_ ~loc:l c then_ else_ ]

(** The statements [make target] computing the value of [e] into a new variable [target],
    and that variable; no variable if [e] is of type unit. *)
and branch ctx (e : Typedtree.expression) make =
  let l = loc e.exp_loc in
  if is_unit e.exp_type then
    let* stmts = make None in
    Ok (stmts, unit_value ~loc:l)
  else
    let* typ = typ ~at:e.exp_loc e.exp_type in
    let x = Names.fresh ctx.names "tmp" in
    let* stmts = make (Some (x, l)) in
    Ok
      ( R.Stmt.local ~loc:l ~const:false ~typ (ident ~loc:l x) @ stmts,
        R.Expr.var ~loc:l (name ~loc:l x) )

and assign (x, l) v =
  R.Stmt.assign ~loc:l [ R.Expr.var ~loc:l (name ~loc:l x) ] (R.Stmt.expr_rhs v)

module S = Caravan_spec.Spec_ast

(** The Raven type of the type [t] written in a contract at [at]. *)
let spec_type ~at (t : S.pty) : (R.Type.t, error) Result.t =
  let l = loc at in
  match t with
  | PTtyapp (Qid { pid_str = "int"; _ }, []) -> Ok (R.Type.int ~loc:l)
  | PTtyapp (Qid { pid_str = "bool"; _ }, []) -> Ok (R.Type.bool ~loc:l)
  | PTtyapp (Qid { pid_str = "unit"; _ }, []) -> Ok (R.Type.tuple ~loc:l [])
  | _ -> unsupported at "This type"

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

(** The head of the application [t] and its arguments. *)
let rec spine (t : S.term) args =
  match t.term_desc with Tapply (f, a) -> spine f (a :: args) | _ -> (t, args)

(** The formula [t] of a contract, with the Raven names of [vars] for the contract's. *)
let rec formula (vars : (string * string) list) (t : S.term) : (R.Expr.t, error) Result.t
    =
  let at = t.term_loc in
  let l = loc at in
  match t.term_desc with
  | Ttrue -> Ok (R.Expr.bool ~loc:l true)
  | Tfalse -> Ok (R.Expr.bool ~loc:l false)
  | Tconst (Pconst_integer (n, None)) -> Ok (R.Expr.int ~loc:l (Int.of_string n))
  | Tconst _ -> unsupported at "This constant"
  | Tvar (Qid { pid_str = x; _ }) ->
      begin match (List.Assoc.find vars x ~equal:String.equal, x) with
      | Some x, _ -> Ok (R.Expr.var ~loc:l (name ~loc:l x))
      | None, "max_int" -> Ok (R.Expr.int ~loc:l Prelude.max_int)
      | None, "min_int" -> Ok (R.Expr.int ~loc:l Prelude.min_int)
      | None, _ -> error at (Printf.sprintf "Unbound name %s" x)
      end
  | Tvar (Qdot _) -> unsupported at "A qualified name"
  | Tinfix _ -> formula vars (S.chain t)
  | Tapply _ -> application vars t
  | Tif (c, a, b) ->
      let* c = formula vars c in
      let* a = formula vars a in
      let* b = formula vars b in
      Ok (R.Expr.ite ~loc:l c a b)
  | Tquant (q, binders, body) ->
      let* bound =
        all binders ~f:(fun (id, ty) ->
            match ty with
            | None -> error id.pid_loc "A bound variable needs a type, as in x: int"
            | Some ty ->
                let* ty = spec_type ~at:id.pid_loc ty in
                let l = loc id.pid_loc in
                Ok
                  ( (id.pid_str, id.pid_str),
                    R.Var.make ~loc:l (ident ~loc:l id.pid_str) ty ))
      in
      let* body = formula (List.map bound ~f:fst @ vars) body in
      let vars = List.map bound ~f:snd in
      Ok
        (match q with
        | Tforall -> R.Expr.forall ~loc:l vars body
        | Texists -> R.Expr.exists ~loc:l vars body)
  | Tattr (_, t) | Tcast (t, _) -> formula vars t
  | Tlet _ | Tmatch _ | Ttuple _ | Told _ | Tfield _ -> unsupported at "This formula"

(** The application [t] of an operator. *)
and application vars (t : S.term) =
  let at = t.term_loc in
  let l = loc at in
  let head, args = spine t [] in
  match (head.term_desc, args) with
  | Tvar (Qid { pid_str = "not"; _ }), [ a ] ->
      let* a = formula vars a in
      Ok (R.Expr.not_ ~loc:l a)
  | Tvar (Qid { pid_str = "-"; pid_fixity = Prefix; _ }), [ a ] ->
      let* a = formula vars a in
      Ok (R.Expr.neg ~loc:l a)
  | Tvar (Qid { pid_str = op; pid_fixity = Infix; _ }), [ a; b ] ->
      begin match spec_binop op with
      | None -> unsupported at (Printf.sprintf "The operator %s" op)
      | Some op -> (
          let* a = formula vars a in
          let* b = formula vars b in
          match op with
          | Div -> Ok (prelude_call ~loc:l Prelude.div [ a; b ])
          | Mod -> Ok (prelude_call ~loc:l Prelude.mod_ [ a; b ])
          | _ -> Ok (R.Expr.binary ~loc:l op a b))
      end
  | _ -> unsupported at "A call of a function in a contract"

type func = {
  id : Ident.t;
  raven_name : string;
  params : Typedtree.function_param list;
  body : Typedtree.expression;
  loc : Location.t;
  contract : S.contract option;
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

(** The procedure of [f]. *)
let proc (functions : (string * string) list) origins (f : func) :
    (R.Callable.t, error) Result.t =
  let names = Names.create () in
  let ctx = { names; functions; origins } in
  let l = loc f.loc in
  let* formals =
    all f.params ~f:(fun (p : Typedtree.function_param) ->
        match p.fp_kind with
        | Tparam_pat { pat_desc = Tpat_var (id, _, _); pat_type; pat_loc; _ }
          when Poly.equal p.fp_arg_label Asttypes.Nolabel ->
            let* typ = typ ~at:pat_loc pat_type in
            let x = Names.bind names id in
            Ok
              ( Some (Ident.name id, x),
                range_spec ~loc:(loc pat_loc) pat_type x,
                R.Var.make ~loc:(loc pat_loc) (ident ~loc:(loc pat_loc) x) typ )
        | Tparam_pat
            { pat_desc = Tpat_construct (_, { cstr_name = "()"; _ }, [], _); pat_loc; _ }
          ->
            let x = Names.fresh names "unit" in
            let l = loc pat_loc in
            Ok (None, None, R.Var.make ~loc:l (ident ~loc:l x) (R.Type.tuple ~loc:l []))
        | _ -> unsupported p.fp_loc "This parameter")
  in
  let header = Option.bind f.contract ~f:(fun c -> c.header) in
  let* result_name, arg_names = contract_names f header (List.length formals) in
  let result = Names.fresh names result_name in
  let* returns =
    if is_unit f.body.exp_type then Ok []
    else
      let* typ = typ ~at:f.body.exp_loc f.body.exp_type in
      Ok [ R.Var.make ~loc:l (ident ~loc:l result) typ ]
  in
  (* The names the contract uses: the parameters' and the result's. *)
  let params =
    List.map2_exn arg_names formals ~f:(fun contract_name (ocaml, _, var) ->
        let raven = Option.value_map ocaml ~default:"" ~f:snd in
        Option.map contract_name ~f:(fun n -> (n, raven)))
    |> List.filter_map ~f:Fn.id
  in
  let vars = (result_name, result) :: params in
  let specs fs =
    all fs ~f:(fun f -> Result.map (formula vars f) ~f:(fun e -> R.Spec.make e))
  in
  (* Values of type [int] are in its range. *)
  let in_range = List.filter_map formals ~f:(fun (_, range, _) -> range) in
  let result_in_range =
    if List.is_empty returns then None else range_spec ~loc:l f.body.exp_type result
  in
  let* requires =
    specs (Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires))
  in
  let* ensures =
    specs (Option.value_map f.contract ~default:[] ~f:(fun c -> c.ensures))
  in
  let requires = in_range @ requires in
  let ensures = Option.to_list result_in_range @ ensures in
  let* stmts, v = expr ctx f.body in
  let body =
    if List.is_empty returns then stmts
    else
      stmts
      @ [
          R.Stmt.assign ~loc:l
            [ R.Expr.var ~loc:l (name ~loc:l result) ]
            (R.Stmt.expr_rhs v);
        ]
  in
  Ok
    (R.Callable.proc ~loc:l
       ~formals:(List.map formals ~f:(fun (_, _, v) -> v))
       ~returns ~requires ~ensures (ident ~loc:l f.raven_name) (Some body))

(** The contract annotating the item at [item_loc], ending before [next]: an annotation in
    between. *)
let contract_after (annotations : Annotation.t list) ~(item_loc : Location.t)
    ~(next : Location.t option) : (S.contract option, error) Result.t =
  let after (a : Annotation.t) =
    a.loc.loc_start.pos_cnum >= item_loc.loc_end.pos_cnum
    && Option.for_all next ~f:(fun next ->
        a.loc.loc_end.pos_cnum <= next.loc_start.pos_cnum)
  in
  match List.filter annotations ~f:after with
  | [] -> Ok None
  | [ a ] -> Result.map (Annotation.contract a) ~f:Option.some
  | _ :: a :: _ -> error a.loc "A function has at most one contract"

(** The functions of [structure], with the contracts in [annotations]. *)
let functions (structure : Typedtree.structure) (annotations : Annotation.t list) :
    (func list, error) Result.t =
  let items = structure.str_items in
  let nexts =
    List.map (List.drop items 1) ~f:(fun (i : Typedtree.structure_item) -> Some i.str_loc)
    @ [ None ]
  in
  let* funcs =
    all (List.zip_exn items nexts) ~f:(fun ((item : Typedtree.structure_item), next) ->
        match item.str_desc with
        | Tstr_value (_, bindings) ->
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
                      }
                | _ -> unsupported vb.vb_loc "This definition")
        | _ -> unsupported item.str_loc "This structure item")
  in
  Ok (List.concat funcs)

(** The Raven program of [source]. *)
let program (source : Source.t) : (R.Program.t * origin list, error) Result.t =
  let annotations = Annotation.of_comments source.comments in
  let* funcs = functions source.typed annotations in
  let functions = List.map funcs ~f:(fun f -> (Ident.unique_name f.id, f.raven_name)) in
  let origins = ref [] in
  let* procs = all funcs ~f:(proc functions origins) in
  let file_start = { Lexing.dummy_pos with pos_fname = source.file } in
  Ok
    ( R.Program.make
        ~loc:(R.Loc.make file_start file_start)
        (Prelude.members @ List.map procs ~f:R.Member.callable),
      !origins )
