(** Functions and their contracts, translated to Raven procedures, with atomic updates and
    invariant establishment. *)

open Base
open Translate_context
open Spec_terms
open Proof_terms
open Atomic_proofs
open Expressions

type func = {
  id : Ident.t;
  namespace : string list;
  paths : Path.t list;
  environment : Env.t;
  signature_sites : Module_inventory.signature_value list;
  scheme_type : Types.type_expr;
  source_scheme : Polymorphic_functions.scheme option;
  lexical_owner : Ident.t option;
  raven_name : string;
  params : Typedtree.function_param list;
  body : Typedtree.expression;
  loc : Location.t;
  name_loc : Location.t;
  contract : S.contract option;
  contract_origin : Annotation.t option;
      (** The selected source contract, absent for inferred contracts. *)
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

(** Ghost header variables are inferred from the native signature and checked contract
    expressions, independently of the compiler's choice of variable names. *)
let ghost_signature ?(flexible = []) ~parameters (f : func) =
  let inputs = ghost_params f in
  let outputs = ghost_results f in
  let declarations = inputs @ outputs in
  let header = Option.bind f.contract ~f:(fun contract -> contract.S.header) in
  let* result_name, argument_names = contract_names f header (List.length f.params) in
  let parameters_named =
    List.concat_map (List.zip_exn argument_names f.params) ~f:(fun (name, parameter) ->
        match parameter.Typedtree.fp_kind with
        | Tparam_pat pattern | Tparam_optional_default (pattern, _) ->
            Option.to_list (Option.map name ~f:(fun name -> (name, pattern.pat_type)))
            @ List.map (Typedtree.pat_bound_idents_full pattern)
                ~f:(fun (_, name, typ, _) -> (name.txt, typ)))
  in
  let variables = (result_name, f.body.exp_type) :: parameters_named in
  let known_names = List.map declarations ~f:(fun (id, _) -> id.S.pid_str) in
  let known q =
    match q with
    | S.Qid id
      when List.Assoc.mem variables id.pid_str ~equal:String.equal
           || List.mem known_names id.pid_str ~equal:String.equal ->
        true
    | _ ->
        Option.is_some (Source.value_path f.environment q)
        || Option.is_some (Source.constructor f.environment q)
        || Option.is_some (Source.logical_builtin_path ~functions:[] q)
  in
  let witness = function
    | S.Qid id when not (String.is_empty id.pid_str) ->
        Char.is_lowercase id.pid_str.[0] || Char.equal id.pid_str.[0] '_'
    | _ -> false
  in
  let rec functions_known bound (term : S.term) =
    let check = functions_known bound in
    let rec callable (callee : S.term) =
      match callee.term_desc with
      | Tvar (Qid id) when List.mem bound id.pid_str ~equal:String.equal -> true
      | Tvar q -> known q
      | Tapply (callee, argument) -> callable callee && check argument
      | _ -> check callee
    in
    match term.term_desc with
    | Tapply (callee, argument) -> callable callee && check argument
    | Tinfix (left, _, right) -> check left && check right
    | Tif (condition, yes, no) -> check condition && check yes && check no
    | Tquant (_, binders, body) ->
        functions_known (List.map binders ~f:(fun (id, _) -> id.S.pid_str) @ bound) body
    | Tcomprehension ((id, _), body) -> functions_known (id.pid_str :: bound) body
    | Tlet (pattern, rhs, body) ->
        check rhs && functions_known (pat_names pattern @ bound) body
    | Tmatch (value, cases) ->
        check value
        && List.for_all cases ~f:(fun (pattern, body) ->
            functions_known (pat_names pattern @ bound) body)
    | Ttuple values -> List.for_all values ~f:check
    | Trecord (base, fields) -> List.for_all (S.record_terms base fields) ~f:check
    | Tattr (_, value) | Tcast (value, _) | Told value | Tfield (value, _) -> check value
    | Ttrue | Tfalse | Tconst _ | Tvar _ -> true
  in
  let rec constraints (term : S.term) =
    if
      functions_known [] term
      && List.for_all (term_references [] term) ~f:(fun q -> known q || witness q)
    then [ term ]
    else
      match term.term_desc with
      | Tinfix (left, { pid_str = "&&"; _ }, right)
      | Tapply
          ( {
              term_desc =
                Tapply ({ term_desc = Tvar (Qid { pid_str = "&&"; _ }); _ }, left);
              _;
            },
            right ) ->
          constraints left @ constraints right
      | Tattr (_, term) -> constraints term
      | _ -> []
  in
  let terms =
    Option.value_map f.contract ~default:[] ~f:(fun contract ->
        contract.requires @ contract.atomic_requires @ contract.ensures
        @ contract.atomic_ensures)
  in
  let constraints = List.concat_map terms ~f:constraints in
  let witnesses =
    List.concat_map constraints ~f:(term_references [])
    |> List.filter_map ~f:(function
      | S.Qid id as q when not (known q) -> Some id.pid_str
      | _ -> None)
    |> List.dedup_and_sort ~compare:String.compare
    |> List.map ~f:(fun name -> (name, Ctype.newvar ()))
  in
  let* declarations, variables, specialization =
    Source.infer_ghost_bindings ~flexible f.environment ~at:f.loc ~parameters
      ~variables:(variables @ witnesses) ~constraints declarations
  in
  let inputs, outputs = List.split_n declarations (List.length inputs) in
  let named = List.map ~f:(fun (id, typ) -> (id.S.pid_str, typ)) in
  Ok (named inputs, named outputs, variables, specialization)

(** The parameters of [f]: their OCaml and Raven names, unless unit, their range, and
    their declarations. A parameter that is a pattern, as [{ tail; _ }], is named as
    [names], those of the contract, name it, and binds its variables at the start of the
    body, by [pattern_params]. *)
let formals ?(names = []) ctx (f : func) =
  let open State.Syntax in
  State.all
    (List.mapi f.params ~f:(fun i p -> (i, p)))
    ~f:(fun (i, (p : Typedtree.function_param)) ->
      match p.fp_kind with
      | Tparam_pat { pat_desc = Tpat_var (id, _, _); pat_type; pat_loc; _ }
        when Poly.equal p.fp_arg_label Asttypes.Nolabel ->
          let* typ = State.typ ctx ~at:pat_loc pat_type in
          let* () = State.note_domain ctx.given.types pat_type in
          let+ x = State.bind_name ~typ:pat_type id in
          let spec =
            match witness_condition ctx ~loc:(loc pat_loc) f.id i x with
            | Some condition -> Some (R.Spec.make condition)
            | None -> value_spec ctx ~loc:(loc pat_loc) pat_type x
          in
          ( Some (Ident.name id, x),
            spec,
            R.Var.make ~loc:(loc pat_loc) (ident ~loc:(loc pat_loc) x) typ )
      | Tparam_pat
          { pat_desc = Tpat_construct (_, { cstr_name = "()"; _ }, [], _); pat_loc; _ } ->
          let+ x = State.fresh "unit" in
          let l = loc pat_loc in
          (None, None, R.Var.make ~loc:l (ident ~loc:l x) (R.Type.tuple ~loc:l []))
      | Tparam_pat
          { pat_desc = Tpat_any | Tpat_record _ | Tpat_tuple _; pat_type; pat_loc; _ }
        when Poly.equal p.fp_arg_label Asttypes.Nolabel ->
          let* typ = State.typ ctx ~at:pat_loc pat_type in
          let contract_name = Option.join (List.nth names i) in
          let* () = State.note_domain ctx.given.types pat_type in
          let+ x = State.fresh (Option.value contract_name ~default:"arg") in
          let l = loc pat_loc in
          ( Some (Option.value contract_name ~default:"", x),
            value_spec ctx ~loc:l pat_type x,
            R.Var.make ~loc:l (ident ~loc:l x) typ )
      | _ -> State.of_result (unsupported p.fp_loc "This parameter"))

(** The statements binding the variables of the parameters of [f] that are patterns to the
    parts of their values, [formals]. *)
let pattern_params ctx (f : func) formals =
  let open State.Syntax in
  let+ bindings =
    State.all (List.zip_exn f.params formals)
      ~f:(fun ((p : Typedtree.function_param), (ocaml, _, _)) ->
        match (p.fp_kind, ocaml) with
        | ( Tparam_pat
              ({ pat_desc = Tpat_any | Tpat_record _ | Tpat_tuple _; pat_loc; _ } as pat),
            Some (_, x) ) ->
            let l = loc pat_loc in
            let value = R.Expr.var ~loc:l (name ~loc:l x) in
            let* access, cond, binds = pattern ctx pat value in
            begin match cond with
            | Some _ ->
                State.of_result (unsupported pat_loc "A refutable pattern as a parameter")
            | None ->
                let* stmts =
                  State.all binds ~f:(fun (id, value, t) ->
                      let* typ = State.typ ctx ~at:pat_loc t in
                      let* () = State.note_domain ctx.given.types t in
                      let+ y = State.bind_name ~typ:t id in
                      R.Stmt.local ~loc:l ~const:true ~typ ~init:(R.Stmt.expr_rhs value)
                        (ident ~loc:l y)
                      @ assert_admissible ctx ~loc:l t y)
                in
                (* The variables of a record's fields are its fields. *)
                let+ () =
                  match pat.pat_desc with
                  | Tpat_record (fields, _) ->
                      State.iter fields ~f:(fun (_, label, p) ->
                          match p.pat_desc with
                          | Tpat_var (id, _, _) ->
                              let* y = State.find_name id in
                              begin match y with
                              | Some y ->
                                  State.modify_carried (fun c ->
                                      {
                                        c with
                                        fields_of =
                                          (y, (label.lbl_name, value)) :: c.fields_of;
                                      })
                              | None -> State.return ()
                              end
                          | _ -> State.return ())
                  | _ -> State.return ()
                in
                access :: stmts
            end
        | _ -> State.return [])
  in
  List.concat (List.concat bindings)

(** The names that the contract of [f] uses for its result and parameters, with the Raven
    names of the result, [result], and of the parameters, [formals]. *)
let rec contract_env ctx ~spec_funcs (f : func) formals ~result =
  let open State.Syntax in
  let signature =
    Option.bind ctx.given.current_procedure ~f:(fun procedure ->
        List.Assoc.find ctx.given.procedure_signatures procedure ~equal:String.equal)
  in
  let declared_type select id annotation =
    match
      Option.bind signature ~f:(fun signature ->
          List.Assoc.find (select signature) id.S.pid_str ~equal:String.equal)
    with
    | Some typ -> Ok typ
    | None -> source_type ctx.given ~at:id.pid_loc annotation
  in
  let header = Option.bind f.contract ~f:(fun c -> c.header) in
  let* result_name, arg_names =
    State.of_result (contract_names f header (List.length formals))
  in
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
      data = ctx.given.types;
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
    State.all
      (List.mapi declared_inputs ~f:(fun i input -> (i, input)))
      ~f:(fun (i, (id, pty)) ->
        let* () =
          if
            List.Assoc.mem env.vars id.pid_str ~equal:String.equal
            || List.exists (List.take declared_inputs i) ~f:(fun (earlier, _) ->
                String.equal earlier.pid_str id.pid_str)
          then
            State.of_result
              (error id.pid_loc
                 (Printf.sprintf "The ghost parameter %s repeats another contract name"
                    id.pid_str))
          else State.return ()
        in
        let* t =
          State.of_result
            (declared_type (fun signature -> signature.procedure_inputs) id pty)
        in
        let+ raven = State.fresh id.pid_str in
        (id.pid_str, raven, t))
  in
  let env =
    List.fold ghosts ~init:env ~f:(fun env (x, raven, t) ->
        { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
  in
  let declared_outputs = ghost_results f in
  let* output_ghosts =
    State.all
      (List.mapi declared_outputs ~f:(fun i output -> (i, output)))
      ~f:(fun (i, (id, pty)) ->
        let* () =
          if
            List.Assoc.mem env.vars id.pid_str ~equal:String.equal
            || List.exists (List.take declared_outputs i) ~f:(fun (earlier, _) ->
                String.equal earlier.pid_str id.pid_str)
          then
            State.of_result
              (error id.pid_loc
                 (Printf.sprintf "The ghost result %s repeats another contract name"
                    id.pid_str))
          else State.return ()
        in
        let* t =
          State.of_result
            (declared_type (fun signature -> signature.procedure_outputs) id pty)
        in
        let+ raven = State.fresh id.pid_str in
        (id.pid_str, raven, t))
  in
  let* () =
    let preconditions =
      Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires @ c.atomic_requires)
    in
    State.of_result
      (Result.all_unit
         (List.map preconditions ~f:(fun t ->
              match
                List.find output_ghosts ~f:(fun (x, _, _) ->
                    List.mem (term_names t) x ~equal:String.equal)
              with
              | Some (x, _, _) ->
                  error t.term_loc
                    (Printf.sprintf "The ghost result %s is unavailable in a precondition"
                       x)
              | None -> Ok ())))
  in
  let env =
    List.fold output_ghosts ~init:env ~f:(fun env (x, raven, t) ->
        { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
  in
  let* env = pattern_definitions env f in
  let+ implicit = implicit_vars env f in
  let env =
    List.fold implicit ~init:env ~f:(fun env (x, raven, t, _) ->
        { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
  in
  (result_name, env, implicit, ghosts)

(** [env] with the names that preconditions of [f] define by a constructor's arguments, as
    [c] in [requires node === Next (v, c)]: the value's fields. *)
and pattern_definitions env (f : func) =
  let open State.Syntax in
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
            let+ v = State.attempt (Spec_terms.formula env value) in
            match (find_constructor ?occurrence:(term_type env value) env q, v) with
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
        | _ -> State.return env
        end
    | _ -> State.return env
  in
  State.fold (List.concat_map requires ~f:conjuncts) ~init:env ~f:define

(** The names free in the preconditions of [f] that [env] does not bind: implicit ghost
    parameters, as [n] in [requires own c.count n], with their Raven names, OCaml types
    and declarations. A name owned as the value of a field has that field's type. *)
and implicit_vars env (f : func) =
  let requires =
    Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires @ c.atomic_requires)
  in
  State.map (free_typed env requires ~at:f.loc) ~f:(fun free ->
      List.map free ~f:(fun (x, raven, t, typ, l) ->
          ( x,
            raven,
            t,
            R.Var.make ~loc:l ~ghost:true ~implicit:true (ident ~loc:l raven) typ )))

(** Translates each contract channel, quantifying its postcondition-only names. *)
let contract_postconditions env ~at ?atomic posts =
  let open State.Syntax in
  let l = loc at in
  let* free = free_typed env posts ~at in
  match (free, posts) with
  | [], _ | _, [] ->
      State.all posts ~f:(fun t ->
          State.map (Spec_terms.formula env t) ~f:(fun e -> R.Spec.make ?atomic e))
  | _ ->
      let env =
        List.fold free ~init:env ~f:(fun env (x, raven, t, _, _) ->
            { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
      in
      let+ posts = State.all posts ~f:(Spec_terms.formula env) in
      let conj = List.reduce_exn posts ~f:(fun a b -> R.Expr.binary ~loc:l And a b) in
      let vars =
        List.map free ~f:(fun (_, raven, _, typ, var_loc) ->
            R.Var.make ~loc:var_loc (ident ~loc:var_loc raven) typ)
      in
      [ R.Spec.make ?atomic (R.Expr.exists ~loc:l vars conj) ]

(** The function that contracts call for [f], defined by its body; [funcs] are the
    functions it may call, by their compiler paths, and [spec_funcs] by their OCaml names.
    Its postconditions are those of [f], under the preconditions that do not call [f]
    itself: these are proven for the function's value, by induction, which a precondition
    bounding the function's own value, as for the code to not overflow, would make
    circular. *)
let func types ~shared ~ocaml_env ~preds ~funcs ~spec_funcs ~proof_support
    ?declaration_name ?(primitive_namespace = []) ?polymorphic_functions
    ?current_polymorphic ?generic_predicates ?(lifted = []) (f : func) :
    R.Callable.t State.t =
  let ctx =
    {
      given =
        {
          (declaration_inputs types ~shared ~env:ocaml_env ~preds ~spec_funcs
             ~proof_support ~primitive_namespace ?polymorphic_functions
             ?current_polymorphic ?generic_predicates ())
          with
          lifted;
        };
      au = None;
    }
  in
  State.in_procedure
  @@
  let open State.Syntax in
  let l = loc f.loc in
  let* () =
    if f.trusted then
      State.of_result (unsupported f.loc "A trusted function that contracts call")
    else State.return ()
  in
  let* formals = formals ctx f in
  let* result = State.fresh "result" in
  let* _, env, implicit, ghosts = contract_env ctx ~spec_funcs f formals ~result in
  let* () =
    match ghosts with
    | [] -> State.return ()
    | _ -> State.of_result (unsupported f.loc "A pure function with ghost parameters")
  in
  let* () =
    match implicit with
    | [] -> State.return ()
    | _ -> State.of_result (unsupported f.loc "A pure function with ghost parameters")
  in
  let calls_self = refers_to f in
  let clauses select = Option.value_map f.contract ~default:[] ~f:select in
  let* requires =
    State.all
      (List.filter (clauses (fun c -> c.requires)) ~f:(fun t -> not (calls_self t)))
      ~f:(Spec_terms.formula env)
  in
  let* ensures = State.all (clauses (fun c -> c.ensures)) ~f:(Spec_terms.formula env) in
  let domains =
    List.filter_mapi (List.zip_exn f.params formals)
      ~f:(fun position ((parameter : Typedtree.function_param), (formal_name, _, _)) ->
        match (parameter.fp_kind, formal_name) with
        | Tparam_pat pattern, Some (_, name) ->
            Option.first_some
              (witness_condition ctx ~loc:l f.id position name)
              (Datatypes.admissible ~loc:l ctx.given.types pattern.pat_type
                 (R.Expr.var ~loc:l (R.Name.make ~loc:l name)))
        | _ -> None)
  in
  let requires = domains @ requires in
  let source_requires = clauses (fun c -> c.requires) in
  let resource_dependent term =
    List.exists (term_references [] term) ~f:(fun q ->
        String.equal (qualid_key q) "own"
        || List.Assoc.mem ctx.given.preds (logical_key env q) ~equal:String.equal
        || Option.is_some (atomic_method env q))
  in
  let result_domain =
    if
      List.exists source_requires ~f:(fun term ->
          calls_self term || resource_dependent term)
    then None
    else
      Datatypes.admissible ~loc:l ctx.given.types f.body.exp_type
        (R.Expr.var ~loc:l (name ~loc:l result))
  in
  let ensures = Option.to_list result_domain @ ensures in
  let ensures =
    List.map ensures ~f:(fun post ->
        R.Spec.make
          (List.fold_right requires ~init:post ~f:(fun pre post ->
               R.Expr.binary ~loc:l Impl pre post)))
  in
  let* result_typ = State.typ ctx ~at:f.body.exp_loc f.body.exp_type in
  let* () = State.note_domain ctx.given.types f.body.exp_type in
  let* bindings =
    State.all (List.zip_exn f.params formals)
      ~f:(fun ((parameter : Typedtree.function_param), (formal, _, _)) ->
        match (parameter.fp_kind, formal) with
        | Tparam_pat pat, Some (_, formal) ->
            let value =
              R.Expr.var ~loc:(loc pat.pat_loc) (name ~loc:(loc pat.pat_loc) formal)
            in
            let* access, condition, bindings = pattern ctx pat value in
            begin match (access, condition) with
            | [], None ->
                State.return
                  (List.map bindings ~f:(fun (id, value, _) ->
                       (Ident.unique_name id, value)))
            | _ :: _, _ ->
                State.of_result
                  (unsupported pat.pat_loc
                     "A mutable parameter pattern in a pure function")
            | [], Some _ ->
                State.of_result
                  (unsupported pat.pat_loc "A refutable pattern as a parameter")
            end
        | _ -> State.return [])
  in
  let+ body = pure ctx ~funcs (List.concat bindings) f.body in
  R.Callable.func ~loc:l
    ~formals:(List.map formals ~f:(fun (_, _, v) -> v))
    ~returns:[ R.Var.make ~loc:l (ident ~loc:l result) result_typ ]
    ~ensures
    (ident ~loc:l (Option.value declaration_name ~default:f.raven_name))
    (Some body)

(** The statements folding, or unfolding with [make], the predicates that the formula [t]
    applies, following its conditionals and matches, as
    [match xs with [] -> stack t [] | _ :: xs' -> stack t xs']. *)
let rec uses ctx env ~(at : Location.t) make (t : S.term) =
  let open State.Syntax in
  let l = loc at in
  let t = S.chain t in
  let head, args = spine t [] in
  match (head.term_desc, args, t.term_desc) with
  | Tvar (Qid { pid_str = "&&" | "/\\"; _ }), [ a; b ], _ ->
      let* a = uses ctx env ~at make a in
      let+ b = uses ctx env ~at make b in
      a @ b
  | Tvar q, _, _
    when List.mem ctx.given.proof_support.opaque_predicates (logical_key env q)
           ~equal:String.equal ->
      State.return []
  | Tvar q, _, _
    when List.Assoc.mem ctx.given.preds (logical_key env q) ~equal:String.equal ->
      let key = logical_key env q in
      let raven, types = List.Assoc.find_exn ctx.given.preds key ~equal:String.equal in
      let generic =
        Option.is_some
          (Generic_predicates.find ~target:raven env.ctx.given.generic_predicates key)
      in
      let* raven =
        Spec_terms.predicate_target env ~at:t.term_loc ~key ~target:raven args
      in
      let pred = if generic then raven else key in
      let+ args =
        Spec_terms.predicate_arguments env ~at:t.term_loc ~display:(qualid_key q) key
          types args
      in
      make ~loc:l ~pred (qualified_name ~loc:l raven) args
  | _, _, Tif (c, a, b) ->
      let* c = Spec_terms.formula env c in
      let* a = uses ctx env ~at make a in
      let+ b = uses ctx env ~at make b in
      if List.is_empty a && List.is_empty b then []
      else [ R.Stmt.ghost_block ~loc:l [ R.Stmt.if_ ~loc:l c a b ] ]
  | _, _, Tmatch (scrutinee, cases) ->
      let* v = Spec_terms.formula env scrutinee in
      let scrutinee_type = Result.ok (Spec_terms.equality_term_type env scrutinee) in
      let rec chain = function
        | [] -> State.return []
        | (p, body) :: rest -> begin
            let* cond, binds = State.of_result (spec_pattern env p v) in
            let types =
              Option.value_map scrutinee_type ~default:[]
                ~f:(Spec_terms.pattern_types env p)
            in
            let env =
              List.fold binds
                ~init:{ env with var_types = types @ env.var_types }
                ~f:(fun env (x, v) -> bind env x (Value v))
            in
            let* body = uses ctx env ~at make body in
            match (cond, rest) with
            | None, _ | _, [] -> State.return body
            | Some cond, _ ->
                let+ rest = chain rest in
                if List.is_empty body && List.is_empty rest then []
                else [ R.Stmt.ghost_block ~loc:l [ R.Stmt.if_ ~loc:l cond body rest ] ]
          end
      in
      chain cases
  | _, _, (Tattr (_, t) | Tcast (t, _)) -> uses ctx env ~at make t
  | _ -> State.return []

(** The statements binding the atomic update of the function [self], whose atomic contract
    has the preconditions [pres] and postconditions [posts], and whose implicit parameters
    are [implicit]; [result] is the contract's name for the result, if there is one; and
    the update. A step inside the update unfolds the predicates of [pres], and folds those
    of [posts] if it commits, and those of [pres] if it aborts. *)
let atomic_update ctx env ~at ~self ~role ~result ~raising ~raised_posts implicit ~pres
    ~posts ~past_results =
  let open State.Syntax in
  let* phi = State.fresh "phi" in
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
    State.map (State.all terms ~f:(uses ctx env ~at make)) ~f:List.concat
  in
  let fold ~loc ~pred:_ p args = [ R.Stmt.fold ~loc p args ] in
  let unfold ~loc ~pred:_ p args = [ R.Stmt.unfold ~loc p args ] in
  (* The values of the implicit parameters in the update opened at [at], in new variables,
     with their declarations. *)
  let implicit_values ~at ~const =
    let open State.Syntax in
    let l = loc at in
    State.all implicit ~f:(fun (x, _, t, _) ->
        let* typ = State.typ ctx ~at t in
        let+ v = State.fresh x in
        ( R.Stmt.local ~loc:l ~ghost:true ?const ~typ (ident ~loc:l v),
          R.Expr.var ~loc:l (name ~loc:l v) ))
  in
  let opening ~l values =
    match values with
    | [] -> R.Stmt.call ~loc:l (au_call ~l "openAU" [])
    | _ -> R.Stmt.assign ~loc:l values (R.Stmt.expr_rhs (au_call ~l "openAU" []))
  in
  let open_ ~contents ~at ~unfold:with_unfold =
    let open State.Syntax in
    let l = loc at in
    let* decls = implicit_values ~at ~const:(Some false) in
    let values = List.map decls ~f:snd in
    let* unfolds =
      if with_unfold then each pres ~at unfold (opened values) else State.return []
    in
    let+ invariants =
      if with_unfold then use_invariants ?contents ctx ~at ~fold:false
      else State.return []
    in
    (invariants @ List.concat_map decls ~f:fst @ [ opening ~l values ] @ unfolds, values)
  in
  (* The update's part of the path when it is bound. *)
  let initial : State.au_path =
    { au_state = Pending; au_step = at; au_values = []; au_performing = None }
  in
  let rec au =
    {
      self;
      role;
      ghost_results =
        List.concat_map past_results ~f:(fun (_, _, _, (snapshot, k)) -> [ snapshot; k ]);
      has_result = Option.is_some result;
      open_;
      close;
      raising;
      token = R.Expr.var ~loc:(loc at) (name ~loc:(loc at) phi);
      commit_only;
    }
  and commit_only ~at ~value =
    let open State.Syntax in
    let l = loc at in
    let* decls = implicit_values ~at ~const:None in
    let values = List.map decls ~f:snd in
    let* unfolds = each pres ~at unfold (opened values) in
    let* folds = each posts ~at (with_views ctx fold) (opened ~value values) in
    let+ () =
      State.record_origin
        {
          at;
          code = Commit;
          message =
            "The atomic postcondition may not hold after this step, which linearizes the \
             function";
          related =
            List.map posts ~f:(fun (t : S.term) ->
                (t.term_loc, "The atomic postcondition"));
        }
    in
    let value =
      match raising with
      | None -> value
      | Some typ ->
          R.Expr.tuple ~loc:l
            ((if Option.is_some result then [ value ] else [])
            @ [ no_exception ~loc:l typ ])
    in
    List.concat_map decls ~f:fst
    @ [ opening ~l values ]
    @ unfolds @ folds
    @ [ R.Stmt.call ~loc:l (au_call ~l "commitAU" [ value ]) ]
  and close c ~value ~outcome =
    State.bind State.get ~f:(fun (s : State.state) ->
        let au_path = Option.value s.path.au ~default:initial in
        let at = au_path.au_step in
        let l = loc at in
        (* The values it commits with: the function's results, and its outcome. *)
        let outcome_value =
          Option.map raising ~f:(fun typ ->
              match outcome with
              | Returned -> no_exception ~loc:l typ
              | Raised (e, _) -> raised_exception ~loc:l typ e
              | Outcome o -> o)
        in
        let value =
          match (au.ghost_results, outcome_value) with
          | [], None -> value
          | ghosts, _ ->
              let components =
                (if au.has_result then [ value ] else [])
                @ ghosts @ Option.to_list outcome_value
              in
              begin match components with
              | [ v ] -> v
              | components -> R.Expr.tuple ~loc:l components
              end
        in
        let commit = R.Stmt.call ~loc:l (au_call ~l "commitAU" [ value ]) in
        let open State.Syntax in
        (* The facts that the function ensures about the state after the action. *)
        let established performs =
          State.all past_results ~f:(fun ((p : past), st, _, (snapshot, k)) ->
              match
                ( performs,
                  List.Assoc.find s.path.opened p.inv ~equal:String.equal,
                  List.Assoc.find s.carried.invariants p.inv ~equal:String.equal )
              with
              | Some performed, Some opened, Some args ->
                  let* next, indices, _ =
                    next_state ctx st ~inv_params:st.params args opened performed
                  in
                  let index =
                    match
                      List.Assoc.find indices
                        (List.Assoc.find_exn st.chains p.field ~equal:String.equal)
                        ~equal:String.equal
                    with
                    | Some index -> index
                    | None ->
                        List.Assoc.find_exn opened.indices p.field ~equal:String.equal
                  in
                  let+ e = Spec_terms.formula env p.element in
                  [
                    R.Stmt.assign ~loc:l [ snapshot ]
                      (R.Stmt.expr_rhs
                         (state_of ~loc:l st (grown st (List.map next ~f:fst))));
                    R.Stmt.assign ~loc:l [ k ]
                      (R.Stmt.expr_rhs (R.Expr.index ~loc:l index e));
                  ]
              | _ ->
                  State.of_result
                    (error at
                       "This step linearizes the function, which ensures a fact about \
                        the state after it, but performs no action"))
        in
        (* The atomic postconditions of the outcome, with the environment they are in. *)
        let* posts, posts_env =
          match outcome with
          | Returned | Outcome _ -> State.return (posts, Fn.id)
          | Raised (_, None) ->
              State.of_result
                (unsupported at
                   "Raising an exception value in a function with an atomic contract")
          | Raised (e, Some raised) ->
              let clauses =
                List.filter raised_posts ~f:(fun ((p : S.pat), _) ->
                    match p.pat_desc with
                    | Pconstr ((Qid id | Qdot (_, id)), _) ->
                        String.equal id.pid_str raised
                    | _ -> false)
              in
              let fields =
                Option.value_map (Datatypes.find_ctor ctx.given.types raised) ~default:[]
                  ~f:(fun (_, c) -> c.fields)
              in
              let field f = R.Expr.field ~loc:l e (qualified_name ~loc:l f) in
              (* The payload's pattern variables are its fields. *)
              let bindings (p : S.pat) =
                match p.pat_desc with
                | Pconstr (_, Some { pat_desc = Pid x; _ }) ->
                    List.map (List.take fields 1) ~f:(fun f -> (x.pid_str, field f))
                | Pconstr (_, Some { pat_desc = Ptuple ps; _ }) ->
                    List.filter_map
                      (List.zip_exn ps (List.take fields (List.length ps)))
                      ~f:(fun ((q : S.pat), f) ->
                        match q.pat_desc with
                        | Pid x -> Some (x.pid_str, field f)
                        | _ -> None)
                | _ -> []
              in
              State.return
                ( List.map clauses ~f:snd,
                  fun env ->
                    List.fold
                      (List.concat_map clauses ~f:(fun (p, _) -> bindings p))
                      ~init:env
                      ~f:(fun env (x, v) -> bind env x (Value v)) )
        in
        match c with
        | Commit ->
            let message =
              "The atomic postcondition may not hold after this step, which linearizes \
               the function"
            in
            let* () =
              State.record_origin
                {
                  at;
                  code = Commit;
                  message;
                  related =
                    List.map posts ~f:(fun (t : S.term) ->
                        (t.term_loc, "The atomic postcondition"));
                }
            in
            let* () =
              State.record_origin
                {
                  at;
                  code = Fold;
                  message;
                  related =
                    List.map posts ~f:(fun (t : S.term) ->
                        (t.term_loc, "This part of the atomic postcondition may not hold"));
                }
            in
            let* folds =
              match au_path.au_performing with
              | Some (a, _) ->
                  (* The views follow from the action; the postcondition's other
                     predicates are folded as usual. *)
                  let others ~loc ~pred p args =
                    if performing_updates_view ctx a pred then []
                    else fold ~loc ~pred p args
                  in
                  let* views = perform_views ctx ~at a in
                  let+ others =
                    each posts ~at others (posts_env (opened ~value au_path.au_values))
                  in
                  views @ others
              | None ->
                  each posts ~at (with_views ctx fold)
                    (posts_env (opened ~value au_path.au_values))
            in
            (* The step is the action's, if its step says when. *)
            let performs = Option.map au_path.au_performing ~f:fst in
            let* checked =
              match au_path.au_performing with
              | Some (p, Some condition) ->
                  let+ check =
                    State.check ~at
                      (Printf.sprintf "This step may not perform the action %s"
                         p.performed.action)
                      condition
                  in
                  [ check ]
              | _ -> State.return []
            in
            let* established = established performs in
            let+ closing = use_invariants ?performs ctx ~at ~fold:true in
            checked @ folds @ List.concat established @ [ commit ] @ closing
        | Abort ->
            let* folds = each pres ~at fold (opened au_path.au_values) in
            let+ closing = use_invariants ctx ~at ~fold:true in
            folds @ [ R.Stmt.call ~loc:l (au_call ~l "abortAU" []) ] @ closing
        | Commit_call -> State.return [ commit ])
  in
  let* () = Atomic_proofs.set_path_au initial in
  let+ () =
    State.modify_carried (fun c ->
        { c with au_results = Some { cas_results = []; read_results = [] } })
  in
  let l = loc at in
  ( R.Stmt.local ~loc:l ~ghost:true ~const:true
      ~init:(R.Stmt.expr_rhs (R.Expr.call ~loc:l (name ~loc:l "bindAU") []))
      (ident ~loc:l phi),
    au )

(** The invariants that the conjunctions [terms] apply, with their arguments. *)
let invariant_apps ?(include_opaque = false) ctx env (terms : S.term list) =
  let open State.Syntax in
  let rec apps (t : S.term) =
    let t = S.chain t in
    match spine t [] with
    | { term_desc = Tvar (Qid { pid_str = "&&" | "/\\"; _ }); _ }, [ a; b ] ->
        apps a @ apps b
    | { term_desc = Tvar q; _ }, args ->
        let key = logical_key env q in
        begin match List.Assoc.find ctx.given.preds key ~equal:String.equal with
        | Some (raven, _)
          when List.Assoc.mem ctx.given.shared.persistent
                 (canonical_member ctx.given.shared raven)
                 ~equal:String.equal
               && (include_opaque
                  || not
                       (List.mem ctx.given.proof_support.opaque_predicates key
                          ~equal:String.equal)) ->
            [ (key, args, t.term_loc) ]
        | _ -> []
        end
    | _ -> []
  in
  State.all (List.concat_map terms ~f:apps) ~f:(fun (p, args, at) ->
      let raven, _ = List.Assoc.find_exn ctx.given.preds p ~equal:String.equal in
      let* raven = predicate_target env ~at ~key:p ~target:raven args in
      State.map
        (State.all args ~f:(Spec_terms.formula env))
        ~f:(fun args -> (canonical_member ctx.given.shared raven, args)))

(** Initializer bindings are local to the state record and its establishment. *)
let rec initial_bindings env initialization continuation =
  match initialization with
  | S.Initial_record fields -> continuation env fields
  | Initial_let (pattern, rhs, body) ->
      Proof_terms.proof_binding ~ghost_rhs:true env pattern rhs (fun env ->
          initial_bindings env body continuation)

let initializer_annotation ctx (f : func) =
  let window (a : Annotation.t) =
    a.loc.loc_start.pos_cnum >= f.body.exp_loc.loc_end.pos_cnum
    && Option.for_all f.next ~f:(fun next ->
        a.loc.loc_end.pos_cnum <= next.loc_start.pos_cnum)
    && Poly.equal (Annotation.kind a) Annotation.Initially
  in
  match List.filter ctx.given.annotations ~f:window with
  | [] -> Ok None
  | [ a ] -> Result.map (Annotation.initially a) ~f:(fun initial -> Some (a, initial))
  | _ :: a :: _ -> error a.loc "A constructor has at most one initially annotation"

let check_initial_fields ctx established fields =
  let known =
    List.concat_map ctx.given.shared.structures ~f:(fun st ->
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
  let open State.Syntax in
  let l = loc at in
  match
    List.find ctx.given.shared.structures ~f:(fun st -> String.equal st.invariant inv)
  with
  | None -> State.return [ R.Stmt.fold ~loc:l (qualified_name ~loc:l inv) args ]
  | Some st ->
      begin match initial with
      | None when (not (has_history st)) && List.is_empty st.chains ->
          (* The witnesses are computed. *)
          State.return [ R.Stmt.fold ~loc:l (qualified_name ~loc:l inv) args ]
      | None ->
          State.of_result
            (error f.loc
               (Printf.sprintf
                  "This function establishes %s, whose initial state it gives as (*@ \
                   initially { ... } *)"
                  inv))
      | Some ((a : Annotation.t), initial) ->
          let* values =
            State.all st.fields ~f:(fun (field, raven, _, t, _) ->
                match
                  List.find initial ~f:(fun (x, _) -> String.equal x.S.pid_str field)
                with
                | Some (_, term) ->
                    let+ v = Spec_terms.expected_formula env (Some t) term in
                    (raven, v, term)
                | None
                  when List.exists st.pendings ~f:(fun p ->
                           String.equal p.pending_field field) ->
                    (* No calls wait yet. *)
                    State.return (raven, R.Expr.set ~loc:l [], S.mk_term Ttrue a.loc)
                | None ->
                    State.of_result
                      (error a.loc
                         (Printf.sprintf "The initial state has no field %s" field)))
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
            State.all st.chains ~f:(fun (field, index) ->
                let _, entries_value, term =
                  List.find_exn values ~f:(fun (raven, _, _) ->
                      String.equal raven (st.state ^ "_" ^ field))
                in
                match entries term with
                | Some es ->
                    let+ es = State.all es ~f:(Spec_terms.formula env) in
                    ( [],
                      ( ident ~loc:l index,
                        R.Expr.map_literal ~loc:l
                          (List.mapi es ~f:(fun i e -> (e, R.Expr.int ~loc:l i)))
                          (R.Expr.int ~loc:l 0) ) )
                | None ->
                    let* () =
                      State.modify (fun (s : State.state) ->
                          { s with tables = { s.tables with dynamic_indices = true } })
                    in
                    let l = loc term.term_loc in
                    let* target = State.fresh "initial_index" in
                    let index_type =
                      R.Type.map ~loc:l (R.Type.ref ~loc:l) (R.Type.int ~loc:l)
                    in
                    let+ () =
                      State.record_origin
                        {
                          at = term.term_loc;
                          code = Precondition;
                          message = "The cells of this indexed field may not be distinct";
                          related = [];
                        }
                    in
                    ( R.Stmt.local ~loc:l ~ghost:true ~typ:index_type
                        ~init:
                          (R.Stmt.expr_rhs
                             (Indexed_initialization.call ~loc:l entries_value))
                        (ident ~loc:l target),
                      (ident ~loc:l index, R.Expr.var ~loc:l (name ~loc:l target)) ))
          in
          let index_statements, indices = List.unzip indexed in
          (* The keys of no registrations: an arbitrary key of the declared type. *)
          let* ons =
            State.all st.pendings ~f:(fun p ->
                let+ key = raw_default ctx ~at p.key_type in
                (ident ~loc:l p.pending_on, R.Expr.map_literal ~loc:l [] key))
          in
          let history =
            if has_history st then
              let qn m x = generated_module_member ~loc:l m x in
              let history = history_elements ~loc:l ctx.given.shared.history st in
              let state =
                R.Expr.call ~loc:l
                  (qn (module_name st "state") "state")
                  (grown st (List.map values ~f:(fun (_, v, _) -> v)))
              in
              let location =
                match anchor_location ctx.given.types st.structure_type with
                | Some at ->
                    R.Expr.field ~loc:l
                      (at ~loc:l (List.hd_exn args))
                      (qualified_name ~loc:l (member_name st "history"))
                | None -> List.hd_exn args
              in
              [
                R.Stmt.call ~loc:l
                  (R.Expr.call ~loc:l (name ~loc:l "fpu")
                     [ location; history.initial; history.full state ]);
              ]
            else []
          in
          (* The parts of the invariant, in the initial state. *)
          let bindings =
            List.map values ~f:(fun (raven, v, _) -> (raven, v))
            @ List.map2_exn st.chains indices ~f:(fun (_, index) (_, v) -> (index, v))
            @ List.map2_exn st.pendings ons ~f:(fun p (_, v) -> (p.pending_on, v))
          in
          let parts =
            List.map st.parts ~f:(fun part ->
                R.Stmt.fold ~loc:l
                  (qualified_name ~loc:l part.part_pred)
                  (part_args part ~args bindings))
          in
          State.return
            (List.concat index_statements @ history @ parts
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
let proc ~given ~past_structures ~proc_name ~pure ?declaration_name ?pure_name (f : func)
    : R.Callable.t State.t =
  let ctx =
    {
      given = { given with current_procedure = Some proc_name; manual = f.manual };
      au = None;
    }
  in
  State.in_procedure
  @@
  let open State.Syntax in
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
  let* result_name, arg_names =
    State.of_result (contract_names f header (List.length f.params))
  in
  let* formals = formals ~names:arg_names ctx f in
  let* bound = pattern_params ctx f formals in
  let* () =
    State.iter
      (List.zip_exn (List.zip_exn f.params arg_names) formals)
      ~f:(fun ((parameter, source), (formal, _, _)) ->
        match (parameter.Typedtree.fp_kind, source, formal) with
        | ( Tparam_pat
              {
                pat_desc = Tpat_any | Tpat_var _ | Tpat_record _ | Tpat_tuple _;
                pat_type;
                _;
              },
            Some source,
            Some (_, raven) ) ->
            let* scope = State.get_scope in
            if List.Assoc.mem scope source ~equal:String.equal then State.return ()
            else State.set_scope ((source, (raven, Some pat_type)) :: scope)
        | _ -> State.return ())
  in
  let* () =
    State.modify_carried (fun c ->
        {
          c with
          formals =
            List.map formals ~f:(fun (ocaml, _, _) ->
                match ocaml with
                | Some (_, x) -> R.Expr.var ~loc:l (name ~loc:l x)
                | None -> unit_value ~loc:l);
        })
  in
  let* result = State.fresh result_name in
  let* returns =
    if is_unit f.body.exp_type then State.return []
    else
      let+ typ = State.typ ctx ~at:f.body.exp_loc f.body.exp_type in
      [ R.Var.make ~loc:l (ident ~loc:l result) typ ]
  in
  let* _, env, implicit, ghosts =
    contract_env ctx ~spec_funcs:ctx.given.spec_funcs f formals ~result
  in
  (* A function that may raise returns its outcome, the exception it raised, last. *)
  let* raising =
    match List.Assoc.find ctx.given.raising proc_name ~equal:String.equal with
    | None -> State.return None
    | Some set ->
        let+ typ = State.typ ctx ~at:f.loc outcome_type in
        Some (set, typ)
  in
  let* raised = State.fresh "raised" in
  let raised_var = R.Expr.var ~loc:l (name ~loc:l raised) in
  let* () =
    State.of_result
      begin match raising with
      | None -> Ok ()
      | Some _ when pure -> unsupported f.loc "A pure function that may raise"
      | Some _ -> Ok ()
      end
  in
  let env =
    match raising with
    | None -> env
    | Some _ ->
        {
          (bind env outcome_name (Raven raised)) with
          var_types = (outcome_name, outcome_type) :: env.var_types;
        }
  in
  let* env =
    specialize_shared env
      ~terms:
        (Option.value_map f.contract ~default:[] ~f:(fun contract ->
             contract.requires @ contract.ensures @ contract.atomic_requires
             @ contract.atomic_ensures))
  in
  let ctx = env.ctx in
  let* ghost_returns =
    State.of_result
      (all (ghost_results f) ~f:(fun (id, _) ->
           match
             ( List.Assoc.find env.vars id.pid_str ~equal:String.equal,
               List.Assoc.find env.var_types id.pid_str ~equal:String.equal )
           with
           | Some (Raven raven), Some t -> Ok (id.pid_str, raven, t)
           | _ -> error id.pid_loc "Cannot resolve this ghost result"))
  in
  let* () = State.modify_carried (fun c -> { c with ghost_returns }) in
  let* ghost_return_vars =
    State.all ghost_returns ~f:(fun (_, raven, t) ->
        let+ typ = State.typ ctx ~at:f.loc t in
        R.Var.make ~loc:l ~ghost:true (ident ~loc:l raven) typ)
  in
  let* ghost_formals =
    State.all ghosts ~f:(fun (_, raven, t) ->
        let+ typ = State.typ ctx ~at:f.loc t in
        R.Var.make ~loc:l ~ghost:true (ident ~loc:l raven) typ)
  in
  (* A parameter that a precondition makes a field of a ghost parameter is one. *)
  let* () =
    State.iter
      (field_equations (Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires)))
      ~f:(fun (x, field, g) ->
        let position =
          List.findi arg_names ~f:(fun _ n -> Option.equal String.equal n (Some x))
        in
        match (List.find ghosts ~f:(fun (n, _, _) -> String.equal n g), position) with
        | Some (_, ghost, _), Some (i, _) ->
            begin match List.nth formals i with
            | Some (Some (_, raven), _, _) ->
                State.modify_carried (fun c ->
                    {
                      c with
                      fields_of =
                        (raven, (field, R.Expr.var ~loc:l (name ~loc:l ghost)))
                        :: c.fields_of;
                    })
            | _ -> State.return ()
            end
        | _ -> State.return ())
  in
  (* Ghost statements and invariants in the code can use ghost parameters. *)
  let* scope = State.get_scope in
  let scope =
    List.fold ghosts ~init:scope ~f:(fun scope (x, raven, t) ->
        (x, (raven, Some t)) :: scope)
  in
  let scope =
    List.fold implicit ~init:scope ~f:(fun scope (x, raven, t, _) ->
        (x, (raven, Some t)) :: scope)
  in
  let* () = State.set_scope scope in
  let implicit_decls = implicit in
  let implicit = List.map implicit ~f:(fun (_, _, _, var) -> var) in
  let specs fs =
    State.all fs ~f:(fun f -> State.map (Spec_terms.formula env f) ~f:R.Spec.make)
  in
  (* Values of type [int] are in its range. *)
  let in_range = List.filter_map formals ~f:(fun (_, range, _) -> range) in
  let* () = State.note_domain ctx.given.types f.body.exp_type in
  let result_in_range =
    if List.is_empty returns then None
    else
      match raising with
      | None -> value_spec ctx ~loc:l f.body.exp_type result
      | Some (_, outcome_typ) ->
          Option.map
            (Datatypes.admissible ~loc:l ctx.given.types f.body.exp_type
               (R.Expr.var ~loc:l (name ~loc:l result)))
            ~f:(fun admissible ->
              R.Spec.make
                (R.Expr.binary ~loc:l Impl
                   (R.Expr.binary ~loc:l Eq raised_var (no_exception ~loc:l outcome_typ))
                   admissible))
  in
  let pres = Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires) in
  let* requires = specs pres in
  (* The invariants of the precondition are opened around each atomic step. *)
  let* invariants = invariant_apps ctx env pres in
  let* () =
    State.modify_carried (fun c ->
        { c with invariants = (if f.manual then [] else invariants) })
  in
  (* A snapshot and a position witnessing each fact about an earlier state. *)
  let* history_invariants = invariant_apps ~include_opaque:true ctx env pres in
  let witnesses (p : past) =
    let* st =
      resolve_shared_structure
        ?element_type:(Spec_terms.term_type env p.element)
        env ~at:p.element.term_loc ~invariant:p.inv ~field:p.field
    in
    let p = { p with inv = st.invariant } in
    let* structure =
      match List.Assoc.find history_invariants p.inv ~equal:String.equal with
      | Some (x :: _) ->
          let anchored =
            match anchor_location ctx.given.types st.structure_type with
            | Some at -> at ~loc:l x
            | None -> x
          in
          State.return
            (R.Expr.field ~loc:l anchored
               (qualified_name ~loc:l (member_name st "history")))
      | _ ->
          State.of_result
            (error p.element.term_loc
               (Printf.sprintf
                  "A fact about an earlier state of %s, which the precondition does not \
                   hold"
                  p.inv))
    in
    let* snapshot = State.fresh "snapshot" in
    let* k = State.fresh "position" in
    let var x = R.Expr.var ~loc:l (name ~loc:l x) in
    let+ e = Spec_terms.formula env p.element in
    let decl x typ = R.Var.make ~loc:l ~ghost:true (ident ~loc:l x) typ in
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
        (past_fact ~loc:l ~history:ctx.given.shared.history st ~structure ~field:p.field
           ~snapshot:(var snapshot) ~k:(var k) e) )
  in
  let* past_params = State.all past_pres ~f:witnesses in
  let* past_results = State.all past_posts ~f:witnesses in
  let* () =
    match (raising, past_results) with
    | Some _, _ :: _ ->
        State.of_result
          (unsupported f.loc "A function that may raise with facts about later states")
    | _ -> State.return ()
  in
  let outcome_returns =
    Option.value_map raising ~default:[] ~f:(fun (_, outcome_typ) ->
        [ R.Var.make ~loc:l (ident ~loc:l raised) outcome_typ ])
  in
  let past_formals = List.concat_map past_params ~f:(fun ((_, _, _, d, _), _) -> d) in
  let past_returns = List.concat_map past_results ~f:(fun ((_, _, _, d, _), _) -> d) in
  let* () =
    Atomic_proofs.modify_path (fun path ->
        {
          path with
          positions =
            List.map past_params ~f:(fun ((p, _, e, _, (snapshot, k)), _) ->
                {
                  pos_inv = p.inv;
                  pos_field = p.field;
                  pos_element = e;
                  pos_snapshot = snapshot;
                  pos_k = k;
                });
        })
  in
  let atomic = Option.exists f.contract ~f:(fun c -> c.atomic) in
  let* () =
    if f.manual && f.trusted then
      State.of_result (error f.loc "A manual proof cannot also be trusted")
    else State.return ()
  in
  let atomic_pres =
    Option.value_map f.contract ~default:[] ~f:(fun c -> c.atomic_requires)
  in
  let* atomic_requires =
    State.all atomic_pres ~f:(fun t ->
        State.map (Spec_terms.formula env t) ~f:(fun e -> R.Spec.make ~atomic:true e))
  in
  (* Preconditions without [own] only mention immutable variables, so they hold
     throughout, as in loops. *)
  let* facts =
    specs
      (List.filter pres ~f:(fun t ->
           not (List.mem (term_names t) "own" ~equal:String.equal)))
  in
  let* () = State.modify_carried (fun c -> { c with facts }) in
  (* Names free in the postconditions are existentially quantified, as [j] in
     [ensures own c.count j]. *)
  let postconditions = contract_postconditions env ~at:f.loc in
  let raises_terms set =
    Exceptions.raises_postconditions ctx.given.types ~at:f.loc
      (Option.value_map f.contract ~default:[] ~f:(fun c -> c.raises))
      set
  in
  (* A function over a witness raises, with each constructor, only what it does for it,
     which calls with that constructor rely on. *)
  let witness_raises_terms =
    match
      (raising, List.Assoc.find ctx.given.witness_raising proc_name ~equal:String.equal)
    with
    | Some (set, _), Some (position, sets) ->
        let at = f.loc in
        let witness_name =
          let header =
            Option.bind f.contract ~f:(fun c ->
                Option.bind c.header ~f:(fun h -> List.nth h.hd_args position))
          in
          match
            (header, Option.map (List.nth f.params position) ~f:(fun p -> p.fp_kind))
          with
          | Some (S.Lvar id), _ -> Some id.pid_str
          | _, Some (Tparam_pat { pat_desc = Tpat_var (id, _, _); _ }) ->
              Some (Ident.name id)
          | _ -> None
        in
        Option.value_map witness_name ~default:[] ~f:(fun witness_name ->
            List.filter_map sets ~f:(fun (constructor, constructor_set) ->
                let only =
                  if Poly.equal constructor_set set then None
                  else
                    List.last
                      (Exceptions.raises_postconditions ctx.given.types ~at []
                         constructor_set)
                in
                Option.map only ~f:(fun only ->
                    S.mk_term
                      (Tmatch
                         ( S.mk_term (Tvar (Qid (S.mk_id ~loc:at witness_name))) at,
                           [
                             (Exceptions.constructor_pattern ~at constructor None, only);
                             (Exceptions.pattern ~at Pwild, S.mk_term Ttrue at);
                           ] ))
                      at)))
    | _ -> []
  in
  let* ensures =
    let posts = Option.value_map f.contract ~default:[] ~f:(fun c -> c.ensures) in
    match raising with
    | None -> postconditions posts
    | Some (set, _) ->
        let* normal = postconditions (List.map posts ~f:Exceptions.on_return) in
        let+ exceptional = postconditions (raises_terms set @ witness_raises_terms) in
        normal @ exceptional
  in
  let atomic_posts =
    Option.value_map f.contract ~default:[] ~f:(fun c -> c.atomic_ensures)
  in
  let* atomic_ensures =
    match raising with
    | None -> postconditions ~atomic:true atomic_posts
    | Some _ ->
        (* As the postconditions: when it returns, and when it raises, what its atomic
           raises clauses say. *)
        let* normal =
          postconditions ~atomic:true (List.map atomic_posts ~f:Exceptions.on_return)
        in
        let+ exceptional =
          postconditions ~atomic:true
            (Exceptions.raises_postconditions ~only:false ctx.given.types ~at:f.loc
               (List.map
                  (Option.value_map f.contract ~default:[] ~f:(fun c -> c.atomic_raises))
                  ~f:(fun (p, t) -> (p, Some t)))
               (State.Raises [])
            @ if atomic then witness_raises_terms else [])
        in
        normal @ exceptional
  in
  let* bind_au, au =
    if atomic && not f.manual then
      let+ binding, au =
        atomic_update ctx env ~at:f.loc ~self:proc_name
          ~role:(Option.value f.role ~default:f.id)
          ~result:(Option.some_if (not (List.is_empty returns)) result_name)
          ~raising:(Option.map raising ~f:snd)
          ~raised_posts:
            (Option.value_map f.contract ~default:[] ~f:(fun c -> c.atomic_raises))
          implicit_decls ~pres:atomic_pres ~posts:atomic_posts
          ~past_results:
            (List.map past_results ~f:(fun ((p, st, _, d, w), _) -> (p, st, d, w)))
      in
      (binding, Some au)
    else State.return ([], None)
  in
  let ctx = { ctx with au } in
  let* () =
    match Option.value_map f.contract ~default:[] ~f:(fun c -> c.variant) with
    | [] -> State.return ()
    | v :: _ -> State.of_result (unsupported v.term_loc "A variant")
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
    let* () =
      State.modify (fun (state : State.state) ->
          {
            state with
            warnings =
              Report.warning f.loc
                (Printf.sprintf "%s is trusted: its contract is assumed, not verified"
                   (Ident.name f.id))
              :: state.warnings;
          })
    in
    State.return
      (R.Callable.proc ~loc:l ~formals:all_formals
         ~returns:(returns @ ghost_return_vars @ past_returns @ outcome_returns)
         ~requires ~ensures
         (ident ~loc:l (Option.value declaration_name ~default:proc_name))
         None)
  end
  else
    (* Raising leaves the function with its other results as they are. *)
    let* () =
      State.modify_carried (fun c ->
          {
            c with
            exit =
              Option.map raising ~f:(fun (allowed, _) ->
                  let raises_terms = raises_terms allowed in
                  {
                    State.results =
                      (if List.is_empty returns then []
                       else [ R.Expr.var ~loc:l (name ~loc:l result) ])
                      @ List.map ghost_returns ~f:(fun (_, raven, _) ->
                          R.Expr.var ~loc:l (name ~loc:l raven));
                    allowed;
                    raises_terms;
                  });
          })
    in
    let no_outcome =
      Option.value_map raising ~default:[] ~f:(fun (_, outcome_typ) ->
          [
            R.Stmt.assign ~loc:l [ raised_var ]
              (R.Stmt.expr_rhs (no_exception ~loc:l outcome_typ));
          ])
    in
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
    let* scope = State.get_scope in
    let* () = State.set_scope ((result_name, (result, Some f.body.exp_type)) :: scope) in
    let* last =
      ghost ctx ~after:f.body.exp_loc.loc_end
        ~before:
          (Option.value_map f.next
             ~default:{ f.loc.loc_end with pos_cnum = Int.max_value } ~f:(fun l ->
               l.loc_start))
    in
    let* state = au_state in
    let* () =
      State.of_result
        begin match state with
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
            error f.loc
              "Caravan cannot tell whether this function linearizes on every path"
        end
    in
    (* An invariant that the function establishes, as one creating a structure, is folded at
     its end, after setting the views of its postcondition. *)
    let* establish =
      if f.manual then State.return []
      else
        let posts = Option.value_map f.contract ~default:[] ~f:(fun c -> c.ensures) in
        let* established = invariant_apps ctx env posts in
        let established =
          List.filter established ~f:(fun (p, _) ->
              not (List.exists invariants ~f:(fun (q, _) -> String.equal p q)))
        in
        if List.is_empty established then State.return []
        else
          let only_views ~loc ~pred p args =
            if List.Assoc.mem ctx.given.shared.views pred ~equal:String.equal then
              [ R.Stmt.fold ~loc p args ]
            else []
          in
          let* views =
            State.all posts ~f:(uses ctx env ~at:f.loc (with_views ctx only_views))
          in
          (* Reported at the end of the function. *)
          let at = { f.loc with loc_start = f.loc.loc_end } in
          let* () =
            State.iter established ~f:(fun (inv, _) ->
                State.record_origin
                  {
                    at;
                    code = Fold;
                    message =
                      Printf.sprintf
                        "The invariant %s may not hold when this function returns" inv;
                    related =
                      Option.to_list
                        (Option.map
                           (List.Assoc.find ctx.given.shared.persistent inv
                              ~equal:String.equal) ~f:(fun def -> (def, "The invariant")));
                  })
          in
          let establish initial_env initial =
            let+ folds =
              State.all established ~f:(fun (inv, args) ->
                  establish_invariant ctx ~f ~at ~env:initial_env ~initial inv args)
            in
            List.concat views @ List.concat folds
          in
          let* annotated = State.of_result (initializer_annotation ctx f) in
          let* env = Proof_terms.scope_env ctx in
          match annotated with
          | None -> establish env None
          | Some (annotation, initial) ->
              initial_bindings env initial (fun initial_env fields ->
                  let* () =
                    State.of_result (check_initial_fields ctx established fields)
                  in
                  establish initial_env (Some (annotation, fields)))
    in
    let+ positions = State.gets (fun (s : State.state) -> s.path.positions) in
    let history_returns =
      List.filter_map past_results ~f:(fun ((p, _, element, _, (snapshot, index)), _) ->
          Option.map (known_position positions p.inv p.field element) ~f:(fun position ->
              R.Stmt.assign ~loc:l [ snapshot; index ]
                (R.Stmt.expr_rhs
                   (R.Expr.tuple ~loc:l [ position.pos_snapshot; position.pos_k ]))))
    in
    let body =
      no_outcome @ bind_au @ bound @ first @ stmts @ assignment @ establish @ last
      @ history_returns
    in
    R.Callable.proc ~loc:l ~formals:all_formals
      ~returns:(returns @ ghost_return_vars @ past_returns @ outcome_returns)
      ~requires ~ensures
      (ident ~loc:l (Option.value declaration_name ~default:proc_name))
      (Some body)

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
    atomic update. A call passing a GADT witness's constructor is not such a wrapper. *)
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
            (* A wrapper passing a GADT witness's constructor selects one of its
               callee's behaviors, which has a contract of its own. *)
            let witness =
              List.exists args ~f:(fun (_, arg) ->
                  match arg with
                  | Typedtree.Arg { exp_desc = Texp_construct (_, cstr, _); _ } ->
                      cstr.cstr_generalized
                  | _ -> false)
            in
            Option.some_if
              ((not witness)
              && List.length passed = List.length params
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
let contract_with_origin_after ?scope (annotations : Annotation.t list)
    ~(item_loc : Location.t) ~(next : Location.t option) =
  let after (a : Annotation.t) =
    Declaration_scope.following ?scope ~item_loc ~next a.loc
  in
  match
    List.filter annotations ~f:(fun a ->
        after a && Poly.equal (Annotation.kind a) Annotation.Contract)
  with
  | [] -> Ok None
  | [ a ] -> Result.map (Annotation.contract a) ~f:(fun contract -> Some (contract, a))
  | _ :: a :: _ -> error a.loc "A function has at most one contract"

let contract_after ?scope annotations ~item_loc ~next =
  Result.map
    (contract_with_origin_after ?scope annotations ~item_loc ~next)
    ~f:(Option.map ~f:fst)

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

(** Whether [contract] says its function may raise. *)
let raising_contract (contract : S.contract) =
  not (List.is_empty contract.raises && List.is_empty contract.atomic_raises)

(** The library functions whose contracts say they may raise, by their qualified names:
    exceptions of libraries are not supported yet, so their calls are rejected. *)
let raising_library_calls (libraries : Library_modules.t list) =
  List.concat_map libraries ~f:(fun lib ->
      Option.value_map
        (Result.ok (interface_contracts lib.library))
        ~default:[]
        ~f:(fun contracts ->
          List.filter_map contracts ~f:(fun (name, (contract, _)) ->
              Option.some_if (raising_contract contract) (lib.library_name ^ "." ^ name))))
