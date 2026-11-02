(** Contract terms and formulas, translated to Raven expressions. *)

open Base
open Translate_context

let integer_literal ~at text =
  match Int.of_string_opt text with
  | Some value -> Ok value
  | None ->
      error at
        "This integer literal is outside the supported OCaml int range; use a \
         mathematical expression with smaller literals"

(** The OCaml type of [t], where it is known: a variable's, or a sequence's slice or
    concatenation. *)
let rec term_type env (t : S.term) =
  match (t.term_desc, spine (S.chain t) []) with
  | Tcast (_, ty), _ -> Result.ok (Source.ocaml_type env.ctx.given.env ~at:t.term_loc ty)
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
        (Source.ocaml_type env.ctx.given.env ~at:t.term_loc
           (S.PTtyapp (Qid (S.mk_id ~loc:t.term_loc "set"), [ ty ])))
  | _, ({ term_desc = Tvar q; _ }, _) when Option.is_some (atomic_method env q) ->
      let signature, method_ = Option.value_exn (atomic_method env q) in
      Option.bind (atomic_inputs signature method_) ~f:(fun (_, outputs) ->
          List.hd outputs)
  | _, ({ term_desc = Tvar q; _ }, _) when Option.is_some (logical_signature env q) ->
      List.hd (Option.value_exn (logical_signature env q)).lemma_outputs
  | _, ({ term_desc = Tvar q; _ }, _ :: _) when Option.is_some (runtime_spec env q) ->
      Result.ok
        (Source.infer_logical_expression env.ctx.given.env
           ~functions:(List.map env.funcs ~f:fst)
           ~variables:(Logical_context.variables env)
           t)
  | _, ({ term_desc = Tvar (Qid { pid_str = "to_sequence"; _ }); _ }, [ _ ]) ->
      Result.ok
        (Source.infer_logical_expression ~is_list:(is_list_term env) env.ctx.given.env
           ~functions:(List.map env.funcs ~f:fst)
           ~variables:(Logical_context.variables env)
           t)
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
  | Trecord (Some base, _), _ -> term_type env base
  | Trecord (None, _), _ ->
      Result.ok
        (Source.infer_logical_expression env.ctx.given.env
           ~functions:(List.map env.funcs ~f:fst)
           ~variables:(Logical_context.variables env)
           t)
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
               | Tconstr _ ->
                   Option.bind (Datatypes.instantiated env.data ty) ~f:(fun d ->
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
      Source.infer_logical_expression env.ctx.given.env
        ~functions:(List.map env.funcs ~f:fst)
        ~variables:(Logical_context.variables env)
        t

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
            begin match find_constructor ~occurrence:t env q with
            | Some (_, constructor) -> constructor.args
            | None ->
                Option.value_map (Datatypes.instantiated env.data t) ~default:[]
                  ~f:(fun data ->
                    Option.value_map
                      (List.find data.ctors ~f:(fun constructor ->
                           String.equal constructor.ocaml c))
                      ~default:[]
                      ~f:(fun constructor -> constructor.args))
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

(** The condition under which the value [v] matches the pattern [p] of a contract, [None]
    if it always does, and the names [p] binds, with their values. *)
let rec spec_pattern env (p : S.pat) (v : R.Expr.t) =
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
      let* value = integer_literal ~at n in
      Ok (Some (R.Expr.binary ~loc:l Eq v (R.Expr.int ~loc:l value)), [])
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

let generic_operands env operands =
  let rec generic typ =
    match Datatypes.desc env.data typ with
    | Tvar _ -> Option.is_some (Datatypes.find_variable env.data typ)
    | Tconstr (_, arguments, _) -> List.exists arguments ~f:generic
    | Ttuple components -> List.exists components ~f:(fun (_, typ) -> generic typ)
    | Tpoly (body, []) -> generic body
    | _ -> false
  in
  List.exists operands ~f:(fun operand ->
      Option.exists (term_type env operand) ~f:generic)

(** Generic source values carry no arithmetic or ordering operations. *)
let numeric_check env ~at operands =
  if generic_operands env operands then
    error at
      "Arithmetic and ordering are unavailable for a universally quantified source type"
  else Ok ()

(** Whether the operands [a] and [b] of the comparison [operator], at [id], have types
    that it can compare. *)
let equality_check env (id : S.id) operator a b =
  match operator with
  | "===" | "=/=" ->
      begin match (term_type env a, term_type env b) with
      | Some left, Some right
        when not (Ctype.is_equal env.ctx.given.env false [ left ] [ right ]) ->
          let operator = S.mk_term (Tvar (Qid id)) id.pid_loc in
          let application = S.mk_term (Tapply (operator, a)) a.term_loc in
          let comparison = S.mk_term (Tapply (application, b)) id.pid_loc in
          begin match
            Source.check_logical_expression ~is_list:(is_list_term env) env.ctx.given.env
              ~functions:(List.map env.funcs ~f:fst)
              ~variables:(Logical_context.variables env)
              ~expected:Predef.type_bool comparison
          with
          | Ok () -> Ok ()
          | Error _ ->
              error id.pid_loc "Logical equality requires operands of the same OCaml type"
          end
      | _ -> Ok ()
      end
  | ("=" | "<>") when not (nullary_constructor a || nullary_constructor b) ->
      let* a_type, b_type = equality_operand_types env a b in
      if
        spec_contains_runtime_refs env.ctx a_type
        || spec_contains_runtime_refs env.ctx b_type
      then
        let direct =
          Datatypes.is_heap_ref env.ctx.given.types a_type
          || Datatypes.is_heap_ref env.ctx.given.types b_type
        in
        error id.pid_loc
          (if direct then
             "Structural equality on references is unsupported; use == or != for \
              reference identity"
           else "Structural equality on values containing references is unsupported")
      else Ok ()
  | "==" | "!=" ->
      if nullary_constructor a || nullary_constructor b then Ok ()
      else
        let* a_type = equality_term_type env a in
        let* b_type = equality_term_type env b in
        if mathematical_type env.ctx a_type || mathematical_type env.ctx b_type then
          error id.pid_loc
            "Physical equality on logical values is unsupported; use = or <>"
        else if
          Datatypes.immediate env.ctx.given.types a_type
          || Datatypes.immediate env.ctx.given.types b_type
        then Ok ()
        else
          error id.pid_loc
            "Physical equality on boxed values is unsupported in specifications"
  | _ -> Ok ()

let predicate_instance env ~at ~key ~target args =
  match Generic_predicates.find ~target env.ctx.given.generic_predicates key with
  | None -> Ok None
  | Some worker ->
      let* arguments =
        Generic_predicates.instantiate ~environment:env.ctx.given.env
          ~expand:(Datatypes.expand env.data) ~at worker
          (List.map args ~f:(term_type env))
      in
      Ok (Some (worker, arguments))

let predicate_target env ~at ~key ~target args =
  let open State.Syntax in
  let* instance = State.of_result (predicate_instance env ~at ~key ~target args) in
  match instance with
  | None -> State.return target
  | Some (worker, arguments) ->
      if
        String.equal
          (String.concat ~sep:"." env.ctx.given.primitive_namespace)
          worker.name
      then
        if
          List.equal Types.eq_type worker.variables
            (List.map arguments ~f:(Datatypes.expand env.data))
        then State.return (worker.name ^ "." ^ Generic_predicates.member worker)
        else State.of_result (unsupported at "Polymorphic predicate recursion")
      else
        let+ instance = State.value_instance env.ctx ~at ~target:worker.name ~arguments in
        instance ^ "." ^ Generic_predicates.member worker

open State.Syntax

(** The formula [t] of a contract. *)
let rec formula (env : env) (t : S.term) : R.Expr.t State.t =
  let* () =
    if opaque_module_types env then
      State.of_result
        (Signature_contract.expression ~logical_types:env.data
           ~environment:env.ctx.given.env
           ~predicates:(fun q ->
             Option.map
               (List.Assoc.find env.ctx.given.preds (logical_key env q)
                  ~equal:String.equal)
               ~f:snd)
           ~variables:(Logical_context.variables env)
           t)
    else State.return ()
  in
  let at = t.term_loc in
  let l = loc at in
  match t.term_desc with
  | Ttrue -> State.return (R.Expr.bool ~loc:l true)
  | Tfalse -> State.return (R.Expr.bool ~loc:l false)
  | Tconst (Pconst_integer (n, None)) ->
      let+ value = State.of_result (integer_literal ~at n) in
      R.Expr.int ~loc:l value
  | Tconst _ -> State.of_result (unsupported at "This constant")
  | Tvar (Qid { pid_str = x; _ }) when is_constructor x -> constructor env t []
  | Tvar (Qdot (_, id)) when is_constructor id.pid_str -> constructor env t []
  | Tvar q when Option.is_some (logical_signature env q) ->
      logical_application env ~at (Option.value_exn (logical_signature env q)) []
  | Tvar (Qid { pid_str = x; _ })
    when List.Assoc.mem env.ctx.given.proof_support.predicate_inputs x ~equal:String.equal
         && not (List.Assoc.mem env.vars x ~equal:String.equal) ->
      application env t
  | Tvar (Qid { pid_str = x; _ }) ->
      begin match (List.Assoc.find env.vars x ~equal:String.equal, x) with
      | Some (Raven x), _ -> State.return (R.Expr.var ~loc:l (name ~loc:l x))
      | Some (Value v), _ -> State.return v
      | Some (State fields), _ ->
          (* A record bound by its fields is their constructor's application. *)
          begin match
            Option.bind
              (List.Assoc.find env.var_types x ~equal:String.equal)
              ~f:(logical_record env)
          with
          | Some (d, c, labels) ->
              State.return
                (R.Expr.call ~loc:l
                   (Datatypes.ctor_name ~loc:l d c)
                   (List.map labels ~f:(fun (label, _) ->
                        fst (List.Assoc.find_exn fields label ~equal:String.equal))))
          | None ->
              State.of_result
                (error at
                   (Printf.sprintf "The state %s is used by its fields, as %s.f" x x))
          end
      | None, "max_int" -> State.return (R.Expr.int ~loc:l Prelude.max_int)
      | None, "min_int" -> State.return (R.Expr.int ~loc:l Prelude.min_int)
      | None, _ -> State.of_result (error at (Printf.sprintf "Unbound name %s" x))
      end
  | Tvar q when Option.is_some (collection_builtin env q) ->
      collection_application env ~at (Option.value_exn (collection_builtin env q)) []
  | Tvar q when Option.is_some (resource_operation env q) ->
      logical_application env ~at (Option.value_exn (resource_operation env q)) []
  | Tvar (Qdot (parent, _) as q) when Option.is_some (resource_module env parent) ->
      State.of_result (error at ("Unknown proof module member " ^ qualid_key q))
  | Tvar (Qdot (Qid m, v))
    when String.equal m.pid_str "Permission"
         && List.mem [ "half"; "full" ] v.pid_str ~equal:String.equal ->
      State.return
        (R.Expr.real ~loc:l (if String.equal v.pid_str "half" then 0.5 else 1.0))
  | Tvar (Qdot _) -> State.of_result (unsupported at "A qualified name")
  | Tinfix _ -> formula env (S.chain t)
  | Tapply _ -> application env t
  | Tif (c, a, b) ->
      let* c = formula env c in
      let* a = formula env a in
      let+ b = formula env b in
      R.Expr.ite ~loc:l c a b
  | Tquant (q, binders, body) ->
      let variable ~at x t =
        let* ty = State.of_result (typ env.ctx ~at t) in
        let l = loc at in
        let+ raven = if env.logical_definition then State.fresh x else State.return x in
        (raven, t, R.Var.make ~loc:l (ident ~loc:l raven) ty)
      in
      let* bound =
        State.all binders ~f:(fun (id, ty) ->
            match ty with
            | None ->
                State.of_result
                  (error id.pid_loc "A bound variable needs a type, as in x: int")
            | Some ty -> begin
                let* t =
                  State.of_result (Source.ocaml_type env.ctx.given.env ~at:id.pid_loc ty)
                in
                (* An existential record is one existential per field. *)
                match (q, logical_record env t) with
                | Texists, Some (_, _, fields) ->
                    let+ fields =
                      State.all fields ~f:(fun (label, field_type) ->
                          let+ variable =
                            variable ~at:id.pid_loc
                              (existential_field id.pid_str label)
                              field_type
                          in
                          (label, variable))
                    in
                    (id.pid_str, t, `Record fields)
                | _ ->
                    let+ variable = variable ~at:id.pid_loc id.pid_str t in
                    (id.pid_str, t, `Variable variable)
              end)
      in
      let env =
        List.fold bound ~init:env ~f:(fun env (x, t, binding) ->
            let binding =
              match binding with
              | `Variable (raven, _, _) -> Raven raven
              | `Record fields ->
                  State
                    (List.map fields ~f:(fun (label, (raven, t, _)) ->
                         (label, (R.Expr.var ~loc:l (name ~loc:l raven), t))))
            in
            { (bind env x binding) with var_types = (x, t) :: env.var_types })
      in
      let rec mathematical_record typ =
        match Types.get_desc typ with
        | Tconstr (path, [], _) ->
            begin match Datatypes.find env.data path with
            | Some data when data.mathematical -> true
            | Some { alias = Some typ; _ } -> mathematical_record typ
            | Some _ | None -> false
            end
        | Tpoly (body, []) -> mathematical_record body
        | _ -> false
      in
      let* () =
        State.iter bound ~f:(fun (_, parent_type, binding) ->
            match binding with
            | `Variable (_, typ, _) -> State.note_domain env.data typ
            | `Record _ when mathematical_record parent_type -> State.return ()
            | `Record fields ->
                State.iter fields ~f:(fun (_, (_, typ, _)) ->
                    State.note_domain env.data typ))
      in
      let+ body = formula env body in
      let variables =
        List.concat_map bound ~f:(fun (_, _, binding) ->
            match binding with
            | `Variable v -> [ v ]
            | `Record fields -> List.map fields ~f:snd)
      in
      let vars = List.map variables ~f:(fun (_, _, v) -> v) in
      (* Flattening a mathematical record preserves its original scalar domains. *)
      let ranges =
        List.concat_map bound ~f:(fun (_, parent_type, binding) ->
            let admissible (x, typ, _) =
              Datatypes.admissible ~loc:l env.data typ
                (R.Expr.var ~loc:l (R.Name.make ~loc:l x))
            in
            match binding with
            | `Variable variable -> Option.to_list (admissible variable)
            | `Record fields when mathematical_record parent_type ->
                List.filter_map fields ~f:(fun (_, (x, typ, _)) ->
                    Option.map (range_spec ~loc:l typ x) ~f:(fun _ ->
                        R.Expr.call ~loc:l
                          (R.Name.make ~loc:l Prelude.in_range)
                          [ R.Expr.var ~loc:l (R.Name.make ~loc:l x) ]))
            | `Record fields ->
                List.filter_map fields ~f:(fun (_, variable) -> admissible variable))
      in
      let guard = List.reduce ranges ~f:(fun a b -> R.Expr.binary ~loc:l And a b) in
      begin match (q, guard) with
      | Tforall, None -> R.Expr.forall ~loc:l vars body
      | Tforall, Some g -> R.Expr.forall ~loc:l vars (R.Expr.binary ~loc:l Impl g body)
      | Texists, None -> R.Expr.exists ~loc:l vars body
      | Texists, Some g -> R.Expr.exists ~loc:l vars (R.Expr.binary ~loc:l And g body)
      end
  | Tcomprehension ((id, ty), body) ->
      let* ty = State.of_result (Source.ocaml_type env.ctx.given.env ~at:id.pid_loc ty) in
      let* raven_type = State.of_result (typ env.ctx ~at:id.pid_loc ty) in
      let* () = State.note_domain env.data ty in
      let* raven = State.fresh id.pid_str in
      let env =
        {
          (bind env id.pid_str (Raven raven)) with
          var_types = (id.pid_str, ty) :: env.var_types;
          logical_definition = true;
        }
      in
      let+ body = formula env body in
      let body =
        match
          Datatypes.admissible ~loc:l env.data ty (R.Expr.var ~loc:l (name ~loc:l raven))
        with
        | None -> body
        | Some admissible -> R.Expr.binary ~loc:l And admissible body
      in
      R.Expr.set_compr ~loc:l (R.Var.make ~loc:l (ident ~loc:l raven) raven_type) body
  | Ttuple ts ->
      let+ ts = State.all ts ~f:(formula env) in
      R.Expr.tuple ~loc:l ts
  | Trecord (base, updates) -> record env t base updates
  | Tmatch (scrutinee, cases) ->
      let* v = formula env scrutinee in
      let* scrutinee_type =
        State.of_result (Result.map (equality_term_type env scrutinee) ~f:Option.some)
      in
      spec_match env ~at ?scrutinee_type v cases
  | Tattr (_, t) -> formula env t
  | Tcast (t, ty) ->
      let* ty = State.of_result (Source.ocaml_type env.ctx.given.env ~at ty) in
      let* raven_type = State.of_result (typ env.ctx ~at ty) in
      let+ value = expected_formula env (Some ty) t in
      R.Expr.annotated value raven_type
  | Tfield ({ term_desc = Trecord (base, updates); _ }, Qid field) ->
      begin match
        ( List.find updates ~f:(fun ((u : S.id), _) ->
              String.equal u.pid_str field.pid_str),
          base )
      with
      | Some (_, value), _ -> formula env value
      | None, Some base -> formula env (S.mk_term (Tfield (base, Qid field)) at)
      | None, None ->
          State.of_result
            (error at (Printf.sprintf "This record has no field %s" field.pid_str))
      end
  | Tfield ({ term_desc = Tvar (Qid { pid_str = x; _ }); _ }, Qid { pid_str = label; _ })
    when Option.is_some (state_fields env x) ->
      begin match
        List.Assoc.find (Option.value_exn (state_fields env x)) label ~equal:String.equal
      with
      | Some (v, _) -> State.return v
      | None ->
          State.of_result
            (error at (Printf.sprintf "The state %s has no field %s" x label))
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
          State.of_result
            (error at
               (Printf.sprintf "A contract reads %s.%s through own, as in own %s.%s v" x
                  label x label))
      | None ->
          let+ r = formula env r in
          R.Expr.field ~loc:l r (qualified_name ~loc:l label)
      end
  | Tfield (_, Qdot _) -> State.of_result (unsupported at "A qualified field")
  | Tlet (pattern, value, body) ->
      let* translated = formula env value in
      let* condition, bindings = State.of_result (spec_pattern env pattern translated) in
      let* () =
        match condition with
        | None -> State.return ()
        | Some _ ->
            State.of_result
              (error pattern.pat_loc "A logical let needs an irrefutable pattern")
      in
      let types =
        Option.value_map (term_type env value) ~default:[] ~f:(pattern_types env pattern)
      in
      let env = { env with var_types = types @ env.var_types } in
      formula
        (List.fold bindings ~init:env ~f:(fun env (id, v) -> bind env id (Value v)))
        body
  | Told _ -> State.of_result (unsupported at "This formula")

(** The formula [t], a sequence if it is a list literal and [expected] is a sequence type,
    as [[]] in [queue q []]. *)
and collection_application env ~at (module_name, function_name) args =
  let l = loc at in
  let* args = State.all args ~f:(fun t -> formula env t) in
  match (module_name, function_name, args) with
  | ("Finset" | "Set"), "empty", [] -> State.return (R.Expr.set ~loc:l [])
  | ("Finset" | "Set"), "singleton", [ x ] -> State.return (R.Expr.set ~loc:l [ x ])
  | ("Finset" | "Set"), "mem", [ x; s ] -> State.return (R.Expr.binary ~loc:l In x s)
  | ("Finset" | "Set"), "union", [ a; b ] -> State.return (R.Expr.binary ~loc:l Union a b)
  | ("Finset" | "Set"), "inter", [ a; b ] -> State.return (R.Expr.binary ~loc:l Inter a b)
  | ("Finset" | "Set"), "diff", [ a; b ] -> State.return (R.Expr.binary ~loc:l Diff a b)
  | ("Finset" | "Set"), "subset", [ a; b ] ->
      State.return (R.Expr.binary ~loc:l Subseteq a b)
  | "Finset", "choose", [ s ] ->
      State.return (R.Expr.call ~loc:l (name ~loc:l "choose") [ s ])
  | "Map", "const", [ v ] -> State.return (R.Expr.map_literal ~loc:l [] v)
  | "Map", "get", [ m; k ] -> State.return (R.Expr.index ~loc:l m k)
  | "Map", "set", [ m; k; v ] -> State.return (R.Expr.update ~loc:l m k v)
  | _ ->
      State.of_result
        (error at
           (Printf.sprintf "Unknown logical collection operation or wrong arity: %s.%s"
              module_name function_name))

and expected_formula env (expected : Types.type_expr option) (t : S.term) =
  let* () =
    match expected with
    | Some expected when opaque_module_types env ->
        State.of_result
          (Signature_contract.terms ~expected ~logical_types:env.data
             ~predicates:(fun q ->
               Option.map
                 (List.Assoc.find env.ctx.given.preds (logical_key env q)
                    ~equal:String.equal)
                 ~f:snd)
             ~environment:env.ctx.given.env
             ~variables:(Logical_context.variables env)
             [ t ])
    | Some _ | None -> State.return ()
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
      let+ elements = State.all elements ~f:(formula env) in
      R.Expr.seq ~loc:(loc t.term_loc) elements
  | Some expected, _
    when Option.is_some (logical_record env expected)
         && match t.term_desc with Trecord _ -> true | _ -> false ->
      begin match t.term_desc with
      | Trecord (base, updates) -> record ~expected env t base updates
      | _ -> formula env t
      end
  | Some expected, _
    when begin match fst (spine t []) with
         | { term_desc = Tvar q; _ } ->
             Option.exists (find_constructor env q) ~f:(fun (data, _) ->
                 not (List.is_empty data.parameters))
         | _ -> false
         end ->
      constructor ~expected env t (snd (spine t []))
  | Some expected, _
    when match spine t [] with
         | { term_desc = Tvar (Qid { pid_str = "to_sequence"; _ }); _ }, _ ->
             (not (List.Assoc.mem env.funcs "to_sequence" ~equal:String.equal))
             && not (List.Assoc.mem env.vars "to_sequence" ~equal:String.equal)
         | _ -> false ->
      let* () =
        State.of_result
          (Source.check_logical_expression ~is_list:(is_list_term env) env.ctx.given.env
             ~functions:(List.map env.funcs ~f:fst)
             ~variables:(Logical_context.variables env)
             ~expected t)
      in
      let* value = formula env t in
      let+ ty = State.of_result (typ env.ctx ~at:t.term_loc expected) in
      R.Expr.annotated value ty
  | _ -> formula env t

(** The application [t] of an operator or a constructor. *)
and application env (t : S.term) =
  let at = t.term_loc in
  let l = loc at in
  let head, args = spine t [] in
  match (head.term_desc, args) with
  | Tvar (Qid id), _ when List.Assoc.mem env.vars id.pid_str ~equal:String.equal ->
      State.of_result
        (error head.term_loc "A local proof value cannot be called as a logical function")
  | Tvar q, args when Option.is_some (atomic_method env q) ->
      let signature, method_ = Option.value_exn (atomic_method env q) in
      begin match (method_, atomic_inputs signature method_) with
      | ("pending" | "committed"), Some (inputs, _) ->
          let+ values = typed_arguments env ~at inputs args in
          let values = atomic_arguments ~loc:l signature method_ values in
          let procedure = qualified_name ~loc:l signature.au_procedure in
          if String.equal method_ "pending" then R.Expr.au ~loc:l procedure values
          else R.Expr.au_commit ~loc:l procedure values
      | _ ->
          State.of_result
            (error at "An AU operation is only allowed in a proof expression")
      end
  | Tvar q, _
    when List.Assoc.mem env.ctx.given.proof_support.predicate_inputs (logical_key env q)
           ~equal:String.equal ->
      let key = logical_key env q in
      let raven, types =
        List.Assoc.find_exn env.ctx.given.preds key ~equal:String.equal
      in
      let* raven = predicate_target env ~at ~key ~target:raven args in
      let+ args = predicate_arguments env ~at ~display:(qualid_key q) key types args in
      R.Expr.call ~loc:l (qualified_name ~loc:l raven) args
  | Tvar q, args when Option.is_some (logical_signature env q) ->
      logical_application env ~at (Option.value_exn (logical_signature env q)) args
  | Tvar q, args when Option.is_some (runtime_spec env q) ->
      let target = Qualified_name.to_string (Option.value_exn (runtime_spec env q)) in
      let* target =
        let registry = env.ctx.given.polymorphic_functions in
        match
          if List.is_empty registry.entries then None
          else Source.value_path env.ctx.given.env q
        with
        | Some path when Path_bindings.mem registry path ->
            let* expression =
              State.of_result
                (Source.infer_typed_logical_expression ~is_list:(is_list_term env)
                   env.ctx.given.env ~functions:(List.map env.funcs ~f:fst)
                   ~variables:(Logical_context.variables env)
                   t)
            in
            let rec callee (expression : Typedtree.expression) =
              match expression.exp_desc with
              | Texp_apply (function_, _) -> callee function_
              | Texp_ident (_, _, declaration) -> Some (declaration, expression.exp_type)
              | _ -> None
            in
            begin match callee expression with
            | Some (declaration, occurrence) ->
                State.polymorphic_call env.ctx ~at ~path ~declaration:declaration.val_type
                  ~occurrence ~target
            | None ->
                State.of_result (unsupported at "This polymorphic logical application")
            end
        | Some _ | None -> State.return target
      in
      let+ args = State.all args ~f:(formula env) in
      R.Expr.call ~loc:l (qualified_name ~loc:l target) args
  | Tvar (Qdot (parent, _) as q), _ when Option.is_some (resource_module env parent) ->
      State.of_result (error at ("Unknown proof module member " ^ qualid_key q))
  | Tvar q, args when Option.is_some (collection_builtin env q) ->
      collection_application env ~at (Option.value_exn (collection_builtin env q)) args
  | Tvar (Qid { pid_str = "not"; _ }), [ a ] ->
      let+ a = formula env a in
      R.Expr.not_ ~loc:l a
  | Tvar (Qid { pid_str = "own"; _ }), ([ location; v ] | [ location; v; _ ]) ->
      let expected = location_type env location in
      let* () =
        match (ghost_projection env location, expected) with
        | Some _, Some expected ->
            State.of_result
              (Source.check_logical_expression env.ctx.given.env
                 ~functions:(List.map env.funcs ~f:fst)
                 ~variables:(Logical_context.variables env)
                 ~expected v)
        | _ -> State.return ()
      in
      let* location = location_of env location in
      let* v = expected_formula env expected v in
      let+ fraction =
        match args with
        | [ _; _; fraction ] ->
            let* () =
              match ghost_projection env (List.hd_exn args) with
              | Some (field, _) when resource_field env field ->
                  State.of_result
                    (error at "Resource fields do not take a fractional permission")
              | _ -> State.return ()
            in
            let* permission_type =
              State.of_result
                (Source.ocaml_type env.ctx.given.env ~at
                   (S.PTtyapp
                      (Qdot (Qid (S.mk_id ~loc:at "Permission"), S.mk_id ~loc:at "t"), [])))
            in
            let* () =
              State.of_result
                (Source.check_logical_expression env.ctx.given.env
                   ~functions:(List.map env.funcs ~f:fst)
                   ~variables:(Logical_context.variables env)
                   ~expected:permission_type fraction)
            in
            let+ fraction = formula env fraction in
            [ fraction ]
        | _ -> State.return []
      in
      R.Expr.own ~loc:l ([ location; v ] @ fraction)
  | Tvar (Qid { pid_str = "([])"; _ }), [ s; i ] ->
      let* s = formula env s in
      let+ i = formula env i in
      R.Expr.index ~loc:l s i
  | Tvar (Qid { pid_str = "++"; pid_fixity = Infix; _ }), [ a; b ] ->
      (* Concatenating sequences, as list literals are here. *)
      let operand (t : S.term) =
        match list_literal t with
        | Some elements ->
            let+ elements = State.all elements ~f:(formula env) in
            R.Expr.seq ~loc:(loc t.term_loc) elements
        | None -> formula env t
      in
      let* a = operand a in
      let+ b = operand b in
      R.Expr.call ~loc:l (R.Name.make ~loc:l "++") [ a; b ]
  | Tvar (Qid { pid_str = "-"; pid_fixity = Prefix; _ }), [ a ] ->
      let* () = State.of_result (numeric_check env ~at [ a ]) in
      let+ a = formula env a in
      R.Expr.neg ~loc:l a
  | Tvar (Qid { pid_str = "@"; pid_fixity = Infix; _ }), [ a; b ] ->
      let* a = formula env a in
      let+ b = formula env b in
      R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ "List" ] "++") [ a; b ]
  | Tvar (Qid ({ pid_str = operator; pid_fixity = Infix; _ } as id)), [ a; b ] ->
      begin match spec_binop operator with
      | None ->
          State.of_result (unsupported at (Printf.sprintf "The operator %s" operator))
      | Some op -> (
          let* () =
            State.of_result
              (match operator with
              | "+" | "-" | "*" | "/" | "mod" | "<" | ">" | "<=" | ">=" ->
                  numeric_check env ~at [ a; b ]
              | _ -> Ok ())
          in
          let* () =
            State.of_result
              (match operator with
              | "=" | "<>" | "==" | "!=" | "===" | "=/=" | "&&" | "||" | "/\\" | "\\/"
              | "->" | "<->"
                when generic_operands env [ a; b ] ->
                  Source.check_logical_expression ~is_list:(is_list_term env)
                    env.ctx.given.env ~functions:(List.map env.funcs ~f:fst)
                    ~variables:(Logical_context.variables env)
                    ~expected:Predef.type_bool t
              | _ -> Ok ())
          in
          let* () = State.of_result (equality_check env id operator a b) in
          (* A literal compared with a sequence is one. *)
          let a_type = term_type env a and b_type = term_type env b in
          let* a = expected_formula env b_type a in
          let+ b = expected_formula env a_type b in
          match op with
          | Div -> prelude_call ~loc:l Prelude.div [ a; b ]
          | Mod -> prelude_call ~loc:l Prelude.mod_ [ a; b ]
          | _ -> R.Expr.binary ~loc:l op a b)
      end
  | Tvar (Qid { pid_str = c; _ }), _ when is_constructor c -> constructor env t args
  | Tvar (Qdot (_, id)), _ when is_constructor id.pid_str -> constructor env t args
  | Tvar q, _ :: _
    when List.Assoc.mem env.funcs (logical_key env q) ~equal:String.equal
         && not
              (List.exists env.ctx.given.proof_support.runtime_functions.entries
                 ~f:(fun (_, target) ->
                   String.equal
                     (Qualified_name.to_string target)
                     (List.Assoc.find_exn env.funcs (logical_key env q)
                        ~equal:String.equal))) ->
      let f = logical_key env q in
      (* A predicate's arguments have its parameters' types. *)
      let expected =
        match List.Assoc.find env.ctx.given.preds f ~equal:String.equal with
        | Some (_, types) when List.length types = List.length args ->
            List.map types ~f:Option.some
        | _ -> List.map args ~f:(fun _ -> None)
      in
      let+ args =
        State.all (List.zip_exn expected args) ~f:(fun (expected, a) ->
            expected_formula env expected a)
      in
      let func = List.Assoc.find_exn env.funcs f ~equal:String.equal in
      R.Expr.call ~loc:l (qualified_name ~loc:l func) args
  | Tvar (Qid { pid_str = "to_sequence"; _ }), args ->
      if List.length args <> 1 then
        State.of_result (error at "to_sequence expects a list")
      else
        let* _ =
          State.of_result
            (Source.infer_logical_expression ~is_list:(is_list_term env) env.ctx.given.env
               ~functions:(List.map env.funcs ~f:fst)
               ~variables:(Logical_context.variables env)
               t)
        in
        let+ args = State.all args ~f:(formula env) in
        R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ "Seq" ] "of_list") args
  | Tvar (Qid { pid_str = ("length" | "last" | "drop" | "take") as f; _ }), args -> begin
      let* args = State.all args ~f:(formula env) in
      let length s =
        R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ "Seq" ] "length") [ s ]
      in
      match (f, args) with
      | "length", [ s ] -> State.return (length s)
      | "last", [ s ] ->
          State.return
            (R.Expr.index ~loc:l s
               (R.Expr.binary ~loc:l Minus (length s) (R.Expr.int ~loc:l 1)))
      | "drop", [ n; s ] -> State.return (R.Expr.slice_from ~loc:l s n)
      | "take", [ n; s ] -> State.return (R.Expr.slice_to ~loc:l s n)
      | _ ->
          State.of_result
            (error at
               (Printf.sprintf "%s expects %s" f
                  (if String.equal f "drop" || String.equal f "take" then
                     "a length and a sequence"
                   else "a sequence")))
    end
  | Tvar q, args when Option.is_some (list_function q) ->
      let+ args = State.all args ~f:(formula env) in
      let f = Option.value_exn (list_function q) in
      R.Expr.call ~loc:l (R.Name.make ~loc:l ~path:[ "List" ] f) args
  | _ -> State.of_result (unsupported at "A call of a function in a contract")

and typed_arguments env ~at inputs args =
  let is_list = is_list_term env in
  if List.length args <> List.length inputs then
    State.of_result
      (error at (Printf.sprintf "Expected %d arguments" (List.length inputs)))
  else
    State.all (List.zip_exn inputs args) ~f:(fun (ty, value) ->
        let sequence =
          match Datatypes.desc env.data ty with
          | Tconstr (path, [ _ ], _) ->
              Option.exists (Datatypes.find env.data path) ~f:Datatypes.is_sequence
          | _ -> false
        in
        let* () =
          State.of_result
            (if sequence then
               Signature_contract.terms ~expected:ty ~logical_types:env.data
                 ~predicates:(fun q ->
                   Option.map
                     (List.Assoc.find env.ctx.given.preds (logical_key env q)
                        ~equal:String.equal)
                     ~f:snd)
                 ~environment:env.ctx.given.env
                 ~variables:(Logical_context.variables env)
                 [ value ]
             else
               Source.check_logical_expression ~is_list env.ctx.given.env
                 ~functions:(List.map env.funcs ~f:fst)
                 ~variables:(Logical_context.variables env)
                 ~expected:ty value)
        in
        let* () =
          match term_type env value with
          | Some actual
            when (not sequence)
                 && not (Ctype.is_equal env.ctx.given.env false [ ty ] [ actual ]) ->
              State.of_result
                (error value.term_loc
                   (Stdlib.Format.asprintf "Expected logical type %a but found %a"
                      Printtyp.type_expr ty Printtyp.type_expr actual))
          | _ -> State.return ()
        in
        let* value = expected_formula env (Some ty) value in
        let+ raven_type = State.of_result (typ env.ctx ~at ty) in
        R.Expr.annotated value raven_type)

and predicate_arguments env ~at ?display key types args =
  let target =
    Option.value_map
      (List.Assoc.find env.ctx.given.preds key ~equal:String.equal)
      ~default:key ~f:fst
  in
  let* instance = State.of_result (predicate_instance env ~at ~key ~target args) in
  let types =
    Option.value_map instance ~default:types ~f:(fun (worker, arguments) ->
        Generic_predicates.parameter_types worker arguments)
  in
  match
    List.Assoc.find env.ctx.given.proof_support.predicate_inputs key ~equal:String.equal
  with
  | None ->
      if List.length types = List.length args then
        State.all (List.zip_exn types args) ~f:(fun (ty, value) ->
            expected_formula env (Some ty) value)
      else State.all args ~f:(formula env)
  | Some minimum ->
      let maximum = List.length types and arity = List.length args in
      if arity < minimum || arity > maximum then
        State.of_result
          (error at
             (Printf.sprintf "Predicate %s expects between %d and %d arguments"
                (Option.value display ~default:key)
                minimum maximum))
      else typed_arguments env ~at (List.take types arity) args

and logical_application env ~at signature args =
  let l = loc at in
  let* () =
    if List.length args = List.length signature.lemma_inputs then State.return ()
    else
      State.of_result
        (error at
           (Printf.sprintf "%s expects %d arguments" signature.lemma_raven
              (List.length signature.lemma_inputs)))
  in
  let+ args = typed_arguments env ~at signature.lemma_inputs args in
  let n = qualified_name ~loc:l signature.lemma_raven in
  if signature.lemma_constant then R.Expr.var ~loc:l n else R.Expr.call ~loc:l n args

(** The formula [t], with the names free in it that can be typed existentially quantified,
    as [n] in [own x.next n && lseg n t]. *)
and quantified env (t : S.term) =
  let l = loc t.term_loc in
  let* free = free_typed ~lenient:true env [ t ] ~at:t.term_loc in
  let env =
    List.fold free ~init:env ~f:(fun env (x, raven, ty, _, _) ->
        { (bind env x (Raven raven)) with var_types = (x, ty) :: env.var_types })
  in
  let+ body = formula env t in
  match free with
  | [] -> body
  | _ ->
      let vars =
        List.map free ~f:(fun (_, raven, _, typ, l) ->
            R.Var.make ~loc:l (ident ~loc:l raven) typ)
      in
      R.Expr.exists ~loc:l vars body

(** The location [t], as in [own r.count n]: a field of a variable of known type. *)
and location_of env (t : S.term) =
  let at = t.term_loc in
  let l = loc at in
  let* () =
    let owner = match t.term_desc with Tfield (owner, _) -> owner | _ -> t in
    match term_type env owner with
    | Some typ -> (
        match Types.get_desc (Ctype.expand_head env.ctx.given.env typ) with
        | Tconstr (path, _, _) when opaque_module_path env path ->
            State.of_result
              (error at
                 "Ownership of an abstract module type must be exposed through a \
                  predicate")
        | _ -> State.return ())
    | None -> State.return ()
  in
  match ghost_projection env t with
  | Some (field, owner) ->
      let* () =
        match term_type env owner with
        | None -> State.return ()
        | Some actual
          when Ctype.is_equal env.ctx.given.env false [ field.field_owner ] [ actual ] ->
            State.return ()
        | Some _ ->
            State.of_result
              (error owner.term_loc "This ghost field has a different owner type")
      in
      let* () =
        State.of_result
          (Source.check_logical_expression env.ctx.given.env
             ~functions:(List.map env.funcs ~f:fst)
             ~variables:(Logical_context.variables env)
             ~expected:field.field_owner owner)
      in
      let+ owner = formula env owner in
      R.Expr.field ~loc:l owner (qualified_name ~loc:l (ghost_field_name field))
  | None -> (
      let* () =
        match spine t [] with
        | ( { term_desc = Tvar (Qdot (Qid m, operation)); _ },
            [ { term_desc = Tvar field; _ }; _ ] )
          when String.equal m.pid_str "Ghost" && String.equal operation.pid_str "at" ->
            State.of_result
              (error (S.qualid_loc field) "Unknown or inaccessible ghost field")
        | _ -> State.return ()
      in
      match t.term_desc with
      | Tfield
          ({ term_desc = Tvar (Qid { pid_str = x; _ }); _ }, Qid { pid_str = label; _ })
        -> begin
          let* r = formula env { t with term_desc = Tvar (Qid (S.mk_id ~loc:at x)) } in
          match List.Assoc.find env.var_types x ~equal:String.equal with
          | None ->
              State.of_result
                (error at (Printf.sprintf "The type of %s is not known here" x))
          | Some typ -> begin
              let* field = State.field_of_type env.ctx.given ~at typ label in
              match (field, atomic_in_record env.ctx typ label) with
              | Some field, _ ->
                  State.return (R.Expr.field ~loc:l r (qualified_name ~loc:l field))
              | None, Some atomic -> begin
                  (* An atomic that an immutable record holds. *)
                  let atomic_ref = R.Expr.field ~loc:l r (qualified_name ~loc:l label) in
                  let* field = State.field_of_type env.ctx.given ~at atomic "" in
                  match field with
                  | Some field ->
                      State.return
                        (R.Expr.field ~loc:l atomic_ref (qualified_name ~loc:l field))
                  | None ->
                      State.of_result
                        (error at (Printf.sprintf "%s has no mutable field %s" x label))
                end
              | None, None ->
                  State.of_result
                    (error at (Printf.sprintf "%s has no mutable field %s" x label))
            end
        end
      | Tvar (Qid { pid_str = x; _ }) -> begin
          let* r = formula env t in
          let* field =
            match List.Assoc.find env.var_types x ~equal:String.equal with
            | None ->
                State.of_result
                  (error at (Printf.sprintf "The type of %s is not known here" x))
            | Some typ -> State.field_of_type env.ctx.given ~at typ ""
          in
          match field with
          | Some field ->
              State.return (R.Expr.field ~loc:l r (qualified_name ~loc:l field))
          | None ->
              State.of_result
                (error at
                   (Printf.sprintf "%s is not an atomic, as owned without a field" x))
        end
      | _ -> begin
          (* An atomic given by an expression, as [last s.cells]. *)
          let* field =
            match term_type env t with
            | Some typ -> State.field_of_type env.ctx.given ~at typ ""
            | None -> State.return None
          in
          match field with
          | Some field ->
              let+ r = formula env t in
              R.Expr.field ~loc:l r (qualified_name ~loc:l field)
          | None ->
              State.of_result
                (unsupported at
                   "This location, other than a field of a variable or an atomic,")
        end)

(** The constructor [t], or the application [t] of a constructor to [args]. *)
and constructor ?expected env (t : S.term) args =
  let at = t.term_loc in
  let l = loc at in
  let head, _ = spine t [] in
  let q = match head.term_desc with Tvar q -> q | _ -> Qid (S.mk_id ~loc:at "") in
  let c_name = qualid_key q in
  match find_constructor env q with
  | None ->
      State.of_result
        (error head.term_loc (Printf.sprintf "Unbound constructor %s" c_name))
  | Some (d, c) ->
      let tuple (a : S.term) =
        match a.term_desc with Ttuple ts -> Some ts | _ -> None
      in
      let* args = State.of_result (ctor_args ~at (List.length c.fields) args ~tuple) in
      let* occurrence =
        match expected with
        | Some _ -> State.return expected
        | None when List.is_empty d.parameters || List.is_empty args -> State.return None
        | None ->
            State.map ~f:Option.some
              (State.of_result
                 (Source.infer_logical_expression env.ctx.given.env
                    ~functions:(List.map env.funcs ~f:fst)
                    ~variables:(Logical_context.variables env)
                    t))
      in
      let data, ctor =
        Option.value
          (Option.bind occurrence ~f:(fun occurrence ->
               find_constructor ~occurrence env q))
          ~default:(d, c)
      in
      let* args =
        if Option.is_some occurrence && List.length ctor.args = List.length args then
          State.all (List.zip_exn ctor.args args) ~f:(fun (typ, argument) ->
              expected_formula env (Some typ) argument)
        else State.all args ~f:(formula env)
      in
      let value = R.Expr.call ~loc:l (Datatypes.ctor_name ~loc:l data ctor) args in
      begin match expected with
      | Some expected when not (List.is_empty data.parameters) ->
          let+ typ = State.of_result (typ env.ctx ~at expected) in
          R.Expr.annotated value typ
      | Some _ | None -> State.return value
      end

and record ?expected env (t : S.term) base updates =
  let at = t.term_loc in
  let l = loc at in
  let* record_type =
    match (expected, base) with
    | Some expected, _ -> State.return (Some expected)
    | None, Some base -> State.return (term_type env base)
    | None, None ->
        State.map ~f:Option.some
          (State.of_result
             (Source.infer_logical_expression env.ctx.given.env
                ~functions:(List.map env.funcs ~f:fst)
                ~variables:(Logical_context.variables env)
                t))
  in
  match Option.bind record_type ~f:(logical_record env) with
  | None -> State.of_result (error at "This record is not of a logical record type")
  | Some (data, constructor, fields) ->
      let* () =
        State.iter updates ~f:(fun ((field : S.id), _) ->
            if List.Assoc.mem fields field.pid_str ~equal:String.equal then
              State.return ()
            else
              State.of_result
                (error field.pid_loc
                   (Printf.sprintf "This record has no field %s" field.pid_str)))
      in
      let* arguments =
        State.all fields ~f:(fun (label, field_type) ->
            match
              ( List.find updates ~f:(fun ((field : S.id), _) ->
                    String.equal field.pid_str label),
                base )
            with
            | Some (_, value), _ -> expected_formula env (Some field_type) value
            | None, Some base ->
                formula env (S.mk_term (Tfield (base, Qid (S.mk_id ~loc:at label))) at)
            | None, None ->
                State.of_result
                  (error at (Printf.sprintf "This record has no field %s" label)))
      in
      let value =
        R.Expr.call ~loc:l (Datatypes.ctor_name ~loc:l data constructor) arguments
      in
      begin match expected with
      | Some expected when not (List.is_empty data.parameters) ->
          let+ typ = State.of_result (typ env.ctx ~at expected) in
          R.Expr.annotated value typ
      | Some _ | None -> State.return value
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
            let+ body = quantified (typed env p) body in
            (R.Expr.Default, body)
        | `Ctor ((c : Datatypes.ctor), args), (p, body) ->
            if env.logical_definition then begin
              let* _, bindings = State.of_result (spec_pattern env p v) in
              let env =
                List.fold bindings ~init:env ~f:(fun env (x, value) ->
                    bind env x (Value value))
              in
              let+ body = quantified (typed env p) body in
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
              let+ body = quantified (typed env p) body in
              (R.Expr.Case (ident ~loc:l c.raven, List.map args ~f:var), body)
            end
      in
      let+ cases = State.all flat ~f:case in
      R.Expr.match_ ~loc:l v cases
  | None ->
      let case_body p binds body =
        quantified
          (List.fold binds ~init:(typed env p) ~f:(fun env (x, value) ->
               bind env x (Value value)))
          body
      in
      let rec chain = function
        | [] -> State.of_result (error at "A match needs at least one case")
        | [ (p, body) ] ->
            let* _, binds = State.of_result (spec_pattern env p v) in
            case_body p binds body
        | (p, body) :: rest -> begin
            let* cond, binds = State.of_result (spec_pattern env p v) in
            let* body = case_body p binds body in
            match cond with
            | None -> State.return body
            | Some cond ->
                let+ rest = chain rest in
                R.Expr.ite ~loc:l cond body rest
          end
      in
      chain cases
