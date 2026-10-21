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
  types : Datatypes.t list;
  names : Names.t;
  functions : (string * string) list;
      (** The top-level functions, by the unique name of their OCaml identifier. *)
  origins : origin list ref;
}

let typ ctx ~at t = Datatypes.typ ctx.types ~at t

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
      let* c_stmts, c = expr ctx c in
      let* stmts = branch ctx e (fun target -> conditional ctx ~at c e1 e2 target) in
      Ok (c_stmts @ fst stmts, snd stmts)
  | Texp_let
      ( Nonrecursive,
        [ { vb_pat = { pat_desc = Tpat_var (id, _, _); _ }; vb_expr; _ } ],
        body ) ->
      let* stmts, v = expr ctx vb_expr in
      let* typ = typ ctx ~at:vb_expr.exp_loc vb_expr.exp_type in
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
    let* typ = typ ctx ~at:e.exp_loc e.exp_type in
    let x = Names.fresh ctx.names "tmp" in
    let def = R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs callee) (ident ~loc:l x) in
    Ok (stmts @ def, R.Expr.var ~loc:l (name ~loc:l x))

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
  (* The body of a case, after defining the variables of its pattern. *)
  let case_body binds (rhs : Typedtree.expression) =
    let* defs =
      all binds ~f:(fun (id, value, t) ->
          let* typ = typ ctx ~at t in
          let x = Names.bind ctx.names id in
          Ok
            (R.Stmt.local ~loc:l ~typ ~init:(R.Stmt.expr_rhs value) (ident ~loc:l x)
            @ assume_in_range ~loc:l t x))
    in
    let* stmts, value = expr ctx rhs in
    let assignment =
      Option.value_map target ~default:[] ~f:(fun t -> [ assign t value ])
    in
    Ok (List.concat defs @ stmts @ assignment)
  in
  let not_exhaustive () =
    [ check ctx ~at "This match may not be exhaustive" (R.Expr.bool ~loc:l false) ]
  in
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
              let x = Names.bind ctx.names id in
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
    let* typ = typ ctx ~at:e.exp_loc e.exp_type in
    let x = Names.fresh ctx.names "tmp" in
    let* stmts = make (Some (x, l)) in
    Ok
      ( R.Stmt.local ~loc:l ~const:false ~typ (ident ~loc:l x) @ stmts,
        R.Expr.var ~loc:l (name ~loc:l x) )

and assign (x, l) v =
  R.Stmt.assign ~loc:l [ R.Expr.var ~loc:l (name ~loc:l x) ] (R.Stmt.expr_rhs v)

module S = Caravan_spec.Spec_ast

(** What a name in a contract stands for: a Raven variable, or a value, such as the field
    of a matched value that a pattern names. *)
type bound = Raven of string | Value of R.Expr.t

type env = { data : Datatypes.t list; vars : (string * bound) list }

let bind env x b = { env with vars = (x, b) :: env.vars }

(** The Raven type of the type [t] written in a contract at [at]. *)
let rec spec_type env ~at (t : S.pty) : (R.Type.t, error) Result.t =
  let l = loc at in
  match t with
  | PTtyapp (Qid { pid_str = "int"; _ }, []) -> Ok (R.Type.int ~loc:l)
  | PTtyapp (Qid { pid_str = "bool"; _ }, []) -> Ok (R.Type.bool ~loc:l)
  | PTtyapp (Qid { pid_str = "unit"; _ }, []) -> Ok (R.Type.tuple ~loc:l [])
  | PTtyapp (Qid { pid_str = ("list" | "option") as n; _ }, [ elt ]) ->
      let* elt = spec_type env ~at elt in
      Ok (R.Type.named ~loc:l (R.Name.make ~loc:l (String.capitalize n)) [ elt ])
  | PTtyapp (Qid { pid_str = n; _ }, []) ->
      let declared (d : Datatypes.t) =
        Option.exists d.id ~f:(fun id -> String.equal (Ident.name id) n)
      in
      begin match List.find env.data ~f:declared with
      | Some d ->
          Ok (R.Type.named ~loc:l (R.Name.make ~loc:l ~path:[ d.module_name ] "T") [])
      | None -> error at (Printf.sprintf "Unbound type %s" n)
      end
  | PTtuple ts ->
      let* ts = all ts ~f:(spec_type env ~at) in
      Ok (R.Type.tuple ~loc:l ts)
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

(** The functions of OCaml's standard library on lists that contracts can use, as Raven's
    [List]'s. *)
let list_function : S.qualid -> string option = function
  | Qdot (Qid { pid_str = "List"; _ }, { pid_str = "length"; _ }) -> Some "len"
  | Qdot (Qid { pid_str = "List"; _ }, { pid_str = "mem"; _ }) -> Some "in"
  | _ -> None

(** The head of the application [t] and its arguments. *)
let rec spine (t : S.term) args =
  match t.term_desc with Tapply (f, a) -> spine f (a :: args) | _ -> (t, args)

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
                let* ty = spec_type env ~at:id.pid_loc ty in
                let l = loc id.pid_loc in
                Ok (id.pid_str, R.Var.make ~loc:l (ident ~loc:l id.pid_str) ty))
      in
      let env = List.fold bound ~init:env ~f:(fun env (x, _) -> bind env x (Raven x)) in
      let* body = formula env body in
      let vars = List.map bound ~f:snd in
      Ok
        (match q with
        | Tforall -> R.Expr.forall ~loc:l vars body
        | Texists -> R.Expr.exists ~loc:l vars body)
  | Ttuple ts ->
      let* ts = all ts ~f:(formula env) in
      Ok (R.Expr.tuple ~loc:l ts)
  | Tmatch (scrutinee, cases) ->
      let* v = formula env scrutinee in
      spec_match env ~at v cases
  | Tattr (_, t) | Tcast (t, _) -> formula env t
  | Tlet _ | Told _ | Tfield _ -> unsupported at "This formula"

(** The application [t] of an operator or a constructor. *)
and application env (t : S.term) =
  let at = t.term_loc in
  let l = loc at in
  let head, args = spine t [] in
  match (head.term_desc, args) with
  | Tvar (Qid { pid_str = "not"; _ }), [ a ] ->
      let* a = formula env a in
      Ok (R.Expr.not_ ~loc:l a)
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
  | Tvar q, args when Option.is_some (list_function q) ->
      let* args = all args ~f:(formula env) in
      let f = Option.value_exn (list_function q) in
      Ok (R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ "List" ] f) args)
  | _ -> unsupported at "A call of a function in a contract"

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
and spec_match env ~at v (cases : (S.pat * S.term) list) =
  let l = loc at in
  let flat_arg (p : S.pat) =
    match p.pat_desc with Pwild -> Some None | Pid id -> Some (Some id) | _ -> None
  in
  let rec flat seen = function
    | [] -> Some []
    | [ ((p : S.pat), body) ] when Option.is_some (flat_arg p) ->
        Some [ (`Any (Option.join (flat_arg p)), body) ]
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
                  ~f:(fun rest -> (`Ctor (c, args), body) :: rest)
            | _ -> None
          end
        | _ -> None
        end
  in
  match flat [] cases with
  | Some flat ->
      let case = function
        | `Any id, body ->
            let env =
              Option.value_map id ~default:env ~f:(fun id ->
                  bind env id.S.pid_str (Value v))
            in
            let* body = formula env body in
            Ok (R.Expr.Default, body)
        | `Ctor ((c : Datatypes.ctor), args), body ->
            let var = function
              | None -> ident ~loc:l "_"
              | Some (id : S.id) -> ident ~loc:(loc id.pid_loc) id.pid_str
            in
            let env =
              List.fold args ~init:env ~f:(fun env -> function
                | None -> env
                | Some (id : S.id) -> bind env id.pid_str (Raven id.pid_str))
            in
            let* body = formula env body in
            Ok (R.Expr.Case (ident ~loc:l c.raven, List.map args ~f:var), body)
      in
      let* cases = all flat ~f:case in
      Ok (R.Expr.match_ ~loc:l v cases)
  | None ->
      let case_body binds body =
        formula
          (List.fold binds ~init:env ~f:(fun env (x, value) -> bind env x (Value value)))
          body
      in
      let rec chain = function
        | [] -> error at "A match needs at least one case"
        | [ (p, body) ] ->
            let* _, binds = spec_pattern env p v in
            case_body binds body
        | (p, body) :: rest -> begin
            let* cond, binds = spec_pattern env p v in
            let* body = case_body binds body in
            match cond with
            | None -> Ok body
            | Some cond ->
                let* rest = chain rest in
                Ok (R.Expr.ite ~loc:l cond body rest)
          end
      in
      chain cases

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
let proc types (functions : (string * string) list) origins (f : func) :
    (R.Callable.t, error) Result.t =
  let names = Names.create () in
  let ctx = { types; names; functions; origins } in
  let l = loc f.loc in
  let* formals =
    all f.params ~f:(fun (p : Typedtree.function_param) ->
        match p.fp_kind with
        | Tparam_pat { pat_desc = Tpat_var (id, _, _); pat_type; pat_loc; _ }
          when Poly.equal p.fp_arg_label Asttypes.Nolabel ->
            let* typ = typ ctx ~at:pat_loc pat_type in
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
      let* typ = typ ctx ~at:f.body.exp_loc f.body.exp_type in
      Ok [ R.Var.make ~loc:l (ident ~loc:l result) typ ]
  in
  (* The names the contract uses: the parameters' and the result's. *)
  let params =
    List.map2_exn arg_names formals ~f:(fun contract_name (ocaml, _, var) ->
        let raven = Option.value_map ocaml ~default:"" ~f:snd in
        Option.map contract_name ~f:(fun n -> (n, raven)))
    |> List.filter_map ~f:Fn.id
  in
  let env =
    {
      data = types;
      vars = List.map ((result_name, result) :: params) ~f:(fun (x, r) -> (x, Raven r));
    }
  in
  let specs fs =
    all fs ~f:(fun f -> Result.map (formula env f) ~f:(fun e -> R.Spec.make e))
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
                    }
              | _ -> unsupported vb.vb_loc "This definition")
        in
        Ok ([], funcs)
    | _ -> unsupported item.str_loc "This structure item"
  in
  let* items = all (List.zip_exn items nexts) ~f:item in
  Ok (List.concat_map items ~f:fst, List.concat_map items ~f:snd)

(** The Raven program of [source]. *)
let program (source : Source.t) : (R.Program.t * origin list, error) Result.t =
  let annotations = Annotation.of_comments source.comments in
  let* types, funcs = items source.typed annotations in
  (* Each data type's module, given the ones declared before it. *)
  let* modules =
    all
      (List.mapi types ~f:(fun i d -> (List.take types i, d)))
      ~f:(fun (before, d) -> Datatypes.member before d)
  in
  let functions = List.map funcs ~f:(fun f -> (Ident.unique_name f.id, f.raven_name)) in
  let origins = ref [] in
  let* procs = all funcs ~f:(proc types functions origins) in
  let file_start = { Lexing.dummy_pos with pos_fname = source.file } in
  Ok
    ( R.Program.make
        ~loc:(R.Loc.make file_start file_start)
        (Prelude.members @ modules @ List.map procs ~f:R.Member.callable),
      !origins )
