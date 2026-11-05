(** The generated proofs of atomic steps: loop invariants, invariants opened around steps,
    actions and views, history snapshots, and linearization. *)

open Base
open Translate_context
open Spec_terms
open Proof_terms

(** The specification of the loop whose body is [body], in an annotation between [after]
    and the body, as [while c do (*@ invariant P *) ... done]. *)
let loop_spec ctx ~(after : Location.t) (body : Typedtree.expression) =
  let between (a : Annotation.t) =
    a.loc.loc_start.pos_cnum >= after.loc_end.pos_cnum
    && a.loc.loc_end.pos_cnum <= body.exp_loc.loc_start.pos_cnum
  in
  match
    List.filter ctx.given.annotations ~f:(fun a ->
        between a && Poly.equal (Annotation.kind a) Annotation.Loop)
  with
  | [] ->
      Ok { S.invariants = []; state_invariants = []; loop_variant = []; loop_raises = [] }
  | [ a ] -> Annotation.loop_spec a
  | _ :: a :: _ -> error a.loc "A loop has at most one annotation"

(** The invariants of a loop at [at]: those of [spec], with the variables in scope there,
    the facts that hold throughout the function, and the value domains of variables in
    scope but a [for] loop's [counter], which goes one beyond. Names free in [spec]'s
    invariants are existentially quantified, as [k] in [invariant own i.contents k];
    [relation], given the values these own, as [k] for [i.contents], may add a conjunct,
    as the value of the loop's condition. The invariants of [spec] hold under [guard] if
    given, as for a loop that may raise, when it has not. *)
let rec loop_invariants ?(counter = "") ?guard ctx ~at (spec : S.loop_spec)
    ~(relation : ((string * string) * R.Expr.t) list -> R.Expr.t option State.t) =
  let open State.Syntax in
  let l = loc at in
  let* () =
    State.of_result
      begin match spec.loop_variant with
      | [] -> Ok ()
      | v :: _ -> unsupported v.term_loc "A variant"
      end
  in
  let* scope = scope in
  let* runtime_names =
    State.gets (fun (state : State.state) -> List.map state.names.bound ~f:snd)
  in
  let runtime name = List.mem runtime_names name ~equal:String.equal in
  let* env = scope_env ctx in
  let* env, state_invariants =
    State.fold spec.state_invariants ~init:(env, [])
      ~f:(fun (env, terms) (pattern, body) ->
        let* value, ty = proof_state ~at:pattern.S.pat_loc in
        let* _ = State.of_result (bind_proof_pattern env pattern ty value) in
        let+ source = State.fresh "caravan$loop_state" in
        let id = S.mk_id ~loc:pattern.pat_loc source in
        let variable = S.mk_term (Tvar (Qid id)) pattern.pat_loc in
        let term = S.mk_term (Tlet (pattern, variable, body)) body.term_loc in
        let env =
          {
            (bind env source (Value value)) with
            var_types = (source, ty) :: env.var_types;
          }
        in
        (env, terms @ [ term ]))
  in
  let terms = spec.invariants @ state_invariants in
  let* free = free_typed env terms ~at in
  let env =
    List.fold free ~init:env ~f:(fun env (x, raven, t, _, _) ->
        { (bind env x (Raven raven)) with var_types = (x, t) :: env.var_types })
  in
  let* invariants = State.all terms ~f:(formula env) in
  (* The values that the invariants own, by the Raven names of their references and
     fields. *)
  let* reads =
    State.all (List.concat_map terms ~f:owned_names) ~f:(fun (x, label, v) ->
        match
          ( List.Assoc.find env.vars x ~equal:String.equal,
            List.Assoc.find env.var_types x ~equal:String.equal,
            List.Assoc.find env.vars v ~equal:String.equal )
        with
        | Some (Raven r), Some t, Some (Raven v) ->
            let+ field = State.field_of_type ctx.given ~at t label in
            Option.map field ~f:(fun field ->
                ((r, field), R.Expr.var ~loc:l (name ~loc:l v)))
        | _ -> State.return None)
  in
  let* related = relation (List.filter_opt reads) in
  let* () =
    State.iter scope ~f:(fun (_, (raven, typ)) ->
        if String.equal raven counter || not (runtime raven) then State.return ()
        else
          match typ with
          | None -> State.return ()
          | Some typ -> State.note_domain ctx.given.types typ)
  in
  let+ facts = State.gets (fun (s : State.state) -> s.carried.facts) in
  let invariants = invariants @ Option.to_list related in
  let guarded e =
    R.Spec.make
      (Option.value_map guard ~default:e ~f:(fun g -> R.Expr.binary ~loc:l Impl g e))
  in
  let user =
    match (free, invariants) with
    | _, [] -> []
    | [], _ -> List.map invariants ~f:guarded
    | _, i :: is ->
        let vars =
          List.map free ~f:(fun (_, raven, _, typ, l) ->
              R.Var.make ~loc:l (ident ~loc:l raven) typ)
        in
        let conj = List.fold is ~init:i ~f:(fun a b -> R.Expr.binary ~loc:l And a b) in
        [ guarded (R.Expr.exists ~loc:l vars conj) ]
  in
  let ranges =
    List.filter_map scope ~f:(fun (_, (raven, t)) ->
        if String.equal raven counter then None
        else
          Option.bind t ~f:(fun t ->
              if runtime raven then value_spec ctx ~loc:l t raven
              else range_spec ~loc:l t raven))
  in
  ranges @ facts @ user

(** The names that [t] owns the values of fields of variables as, as [k] for [i.contents]
    in [own i.contents k]: the variable, the field and the name. *)
and owned_names (t : S.term) =
  match (owned_location t, t.term_desc) with
  | Some owned, _ -> [ owned ]
  | None, (Tapply (a, b) | Tinfix (a, _, b)) -> owned_names a @ owned_names b
  | None, Tif (a, b, c) -> owned_names a @ owned_names b @ owned_names c
  | None, (Tattr (_, t) | Tcast (t, _)) -> owned_names t
  | None, _ -> []

(** The reference holding a structure's ghost fields and its allocation kind. *)
let anchor_source (types : Datatypes.t list) (t : Types.type_expr) =
  let itself ~loc:_ e = e in
  match Datatypes.desc types t with
  | Tconstr (p, [ elt ], _) when Datatypes.is_atomic p -> Some (`Atomic elt, itself)
  | Tconstr (p, [ elt ], _) when Datatypes.is_ref p -> Some (`Reference elt, itself)
  | Tconstr _ ->
      begin match Datatypes.instantiated types t with
      | Some { heap = Some (f :: _); _ } -> Some (`Field f.raven_field, itself)
      | Some { heap = None; ctors = [ { ocaml = ""; fields; args; _ } ]; _ } ->
          List.find_map (List.zip_exn fields args) ~f:(fun (label, a) ->
              match Datatypes.desc types a with
              | Tconstr (q, [ elt ], _) when Datatypes.is_atomic q ->
                  Some
                    ( `Atomic elt,
                      fun ~loc e -> R.Expr.field ~loc e (qualified_name ~loc label) )
              | _ -> None)
      | _ -> None
      end
  | _ -> None

let anchor_location types t = Option.map (anchor_source types t) ~f:snd

let anchor types t =
  Option.bind (anchor_source types t) ~f:(fun (source, location) ->
      let tag =
        match source with
        | `Atomic elt -> Datatypes.allocation_tag ~prefix:"atomic_" ~suffix:"" types elt
        | `Reference elt ->
            Datatypes.allocation_tag ~prefix:"ref_" ~suffix:"_contents" types elt
        | `Field field -> Some field
      in
      Option.map tag ~f:(fun tag -> (tag, location)))

(** The reference holding the ghost fields of the structure [e], the first argument of the
    predicate [pred]. *)
let anchored ctx ~loc ~pred (e : R.Expr.t) =
  match List.Assoc.find ctx.given.preds pred ~equal:String.equal with
  | Some (_, t :: _) ->
      begin match anchor_location ctx.given.types t with
      | Some at -> at ~loc e
      | None -> e
      end
  | _ -> e

(** Resolve shared proof declarations in the caller's type context. *)
let specialize_shared env ~terms =
  let open State.Syntax in
  let add entries key value =
    (key, value) :: List.Assoc.remove entries key ~equal:String.equal
  in
  let specialize_owner env worker arguments prefix =
    let shared = env.ctx.given.shared in
    let rebase text =
      Option.value_map
        (String.chop_prefix text ~prefix:(worker.Generic_parameters.name ^ "."))
        ~default:text
        ~f:(fun suffix -> prefix ^ "." ^ suffix)
    in
    let owners =
      List.filter shared.structures ~f:(fun st ->
          Option.exists st.generic ~f:(fun owner -> String.equal owner.name worker.name))
    in
    State.fold owners ~init:env ~f:(fun env st ->
        let owner = Option.value_exn st.generic in
        let project ty =
          List.hd_exn
            (Generic_parameters.parameter_types
               { owner with parameters = [ ty ] }
               arguments)
        in
        let backend = rebase st.backend in
        if
          List.exists env.ctx.given.shared.structures ~f:(fun instance ->
              String.equal instance.invariant backend && Option.is_none instance.generic)
        then State.return env
        else
          let signature signature =
            {
              signature with
              lemma_raven = rebase signature.lemma_raven;
              lemma_inputs = List.map signature.lemma_inputs ~f:project;
              lemma_outputs = List.map signature.lemma_outputs ~f:project;
            }
          in
          let* fields =
            State.all st.fields ~f:(fun (field, raven, typ, source, grows) ->
                let source = project source in
                let+ typ =
                  if
                    List.exists st.pendings ~f:(fun pending ->
                        String.equal pending.pending_field field)
                  then State.return typ
                  else State.of_result (Datatypes.typ env.data ~at:st.at source)
                in
                (field, raven, typ, source, grows))
          in
          let* view_data =
            State.all st.views ~f:(fun ((view : S.predicate), value) ->
                let key = view.pred_name.pid_str in
                let at = view.pred_name.pid_loc in
                let* target, parameters =
                  State.of_result
                    (Report.expect ~at
                       ("The declaration of view " ^ key)
                       (List.Assoc.find st.context.declaration_predicates key
                          ~equal:String.equal))
                in
                let target = rebase target in
                let parameters = List.map parameters ~f:project in
                let old_field = view_field_in shared key in
                let field = rebase old_field in
                let* value_type =
                  State.of_result
                    (Report.expect ~at
                       ("The value parameter of view " ^ key)
                       (List.last parameters))
                in
                let+ typ = State.of_result (Datatypes.typ env.data ~at value_type) in
                ( { view with pred_name = { view.pred_name with pid_str = target } },
                  value,
                  parameters,
                  field,
                  typ ))
          in
          let aliases =
            (backend, (backend, List.map st.params ~f:(fun (_, typ) -> project typ)))
            :: List.map view_data ~f:(fun (view, _, parameters, _, _) ->
                let target = view.S.pred_name.pid_str in
                (target, (target, parameters)))
          in
          let context =
            {
              declaration_predicates =
                aliases
                @ List.map st.context.declaration_predicates
                    ~f:(fun (key, (target, parameters)) ->
                      (key, (rebase target, List.map parameters ~f:project)));
              declaration_functions =
                List.map st.context.declaration_functions ~f:(fun (key, target) ->
                    (key, rebase target));
              declaration_support =
                {
                  st.context.declaration_support with
                  logical_functions =
                    List.map st.context.declaration_support.logical_functions
                      ~f:(fun (key, declaration) -> (key, signature declaration));
                };
            }
          in
          let st =
            {
              st with
              context;
              generic = None;
              invariant = backend;
              backend;
              fields;
              params = List.map st.params ~f:(fun (key, typ) -> (key, project typ));
              structure_type = project st.structure_type;
              views = List.map view_data ~f:(fun (view, value, _, _, _) -> (view, value));
              pendings =
                List.map st.pendings ~f:(fun pending ->
                    { pending with key_type = project pending.key_type });
            }
          in
          let shared = env.ctx.given.shared in
          let views =
            List.fold view_data ~init:shared.views ~f:(fun views (view, _, _, field, _) ->
                add views view.S.pred_name.pid_str field)
          in
          let fields =
            List.map view_data ~f:(fun (_, _, _, field, typ) -> (field, Snapshot typ))
            @
            if has_history st then
              [
                ( member_name st "history",
                  Fixed (history_elements ~loc:R.Loc.none shared.history st).initial );
              ]
            else []
          in
          let anchors =
            match anchor env.data st.structure_type with
            | None -> shared.anchors
            | Some (tag, _) ->
                let existing =
                  Option.value
                    (List.Assoc.find shared.anchors tag ~equal:String.equal)
                    ~default:[]
                in
                let fields =
                  List.fold fields ~init:existing ~f:(fun fields (key, value) ->
                      add fields key value)
                in
                add shared.anchors tag fields
          in
          let shared =
            {
              shared with
              persistent = add shared.persistent backend st.at;
              views;
              anchors;
              structures =
                st
                :: List.filter shared.structures ~f:(fun other ->
                    not (String.equal other.invariant backend));
            }
          in
          let preds =
            List.fold aliases ~init:env.ctx.given.preds ~f:(fun preds (key, value) ->
                add preds key value)
          in
          let predicate_inputs =
            List.fold view_data ~init:env.ctx.given.proof_support.predicate_inputs
              ~f:(fun inputs (view, _, parameters, _, _) ->
                add inputs view.S.pred_name.pid_str (List.length parameters - 1))
          in
          State.return
            {
              env with
              ctx =
                {
                  env.ctx with
                  given =
                    {
                      env.ctx.given with
                      shared;
                      preds;
                      proof_support =
                        { env.ctx.given.proof_support with predicate_inputs };
                    };
                };
            })
  in
  let register env q args at =
    let key = logical_key env q in
    match List.Assoc.find env.ctx.given.preds key ~equal:String.equal with
    | None -> State.return env
    | Some (target, _) ->
        let shared = env.ctx.given.shared in
        if
          not
            (List.Assoc.mem shared.persistent
               (canonical_member shared target)
               ~equal:String.equal
            || List.Assoc.mem shared.views key ~equal:String.equal)
        then State.return env
        else
          let* instance =
            State.of_result (predicate_instance env ~at ~key ~target args)
          in
          begin match instance with
          | None -> State.return env
          | Some (worker, arguments) ->
              let* resolved = predicate_target env ~at ~key ~target args in
              let prefix =
                String.concat ~sep:"." (Qualified_name.of_string resolved).path
              in
              let* env = specialize_owner env worker arguments prefix in
              let shared = env.ctx.given.shared in
              let persistent =
                if List.Assoc.mem shared.persistent target ~equal:String.equal then
                  add shared.persistent resolved at
                else shared.persistent
              in
              State.return
                {
                  env with
                  ctx =
                    {
                      env.ctx with
                      given = { env.ctx.given with shared = { shared with persistent } };
                    };
                }
          end
  in
  let typed_bindings env bindings =
    List.fold bindings ~init:env ~f:(fun env (name, typ) ->
        { (bind env name (Raven name)) with var_types = (name, typ) :: env.var_types })
  in
  let rec local env bindings body =
    let+ specialized = visit (typed_bindings env bindings) body in
    { env with ctx = specialized.ctx }
  and visit env (term : S.term) =
    let term = S.chain term in
    let head, arguments = spine term [] in
    match head.term_desc with
    | Tvar (Qid id) when List.Assoc.mem env.vars id.pid_str ~equal:String.equal ->
        State.fold arguments ~init:env ~f:visit
    | Tvar q
      when List.Assoc.mem env.ctx.given.preds (logical_key env q) ~equal:String.equal ->
        let* env = register env q arguments term.term_loc in
        State.fold arguments ~init:env ~f:visit
    | _ ->
        begin match term.term_desc with
        | Tquant (_, binders, body) ->
            let* bindings =
              State.all binders ~f:(fun (id, annotation) ->
                  match annotation with
                  | None -> State.return None
                  | Some annotation ->
                      let+ typ =
                        State.of_result
                          (source_type env.ctx.given ~at:id.S.pid_loc annotation)
                      in
                      Some (id.pid_str, typ))
            in
            local env (List.filter_opt bindings) body
        | Tcomprehension ((id, annotation), body) ->
            let* typ =
              State.of_result (source_type env.ctx.given ~at:id.S.pid_loc annotation)
            in
            local env [ (id.pid_str, typ) ] body
        | Tlet (pattern, rhs, body) ->
            let* env = visit env rhs in
            let bindings =
              Option.value_map (term_type env rhs) ~default:[]
                ~f:(pattern_types env pattern)
            in
            local env bindings body
        | Tmatch (value, cases) ->
            let* env = visit env value in
            State.fold cases ~init:env ~f:(fun env (pattern, body) ->
                let bindings =
                  Option.value_map (term_type env value) ~default:[]
                    ~f:(pattern_types env pattern)
                in
                local env bindings body)
        | _ ->
            let children =
              match term.term_desc with
              | Ttrue | Tfalse | Tconst _ | Tvar _ -> []
              | Tfield (base, _) | Tattr (_, base) | Tcast (base, _) | Told base ->
                  [ base ]
              | Tapply (left, right) | Tinfix (left, _, right) -> [ left; right ]
              | Tif (condition, yes, no) -> [ condition; yes; no ]
              | Ttuple values -> values
              | Trecord (base, fields) -> Option.to_list base @ List.map fields ~f:snd
              | Tquant _ | Tcomprehension _ | Tlet _ | Tmatch _ -> []
            in
            State.fold children ~init:env ~f:visit
        end
  in
  let shared = env.ctx.given.shared in
  if
    List.exists env.ctx.given.generic_predicates ~f:(fun worker ->
        List.Assoc.mem shared.views worker.Generic_parameters.key ~equal:String.equal
        || Option.exists
             (List.Assoc.find env.ctx.given.preds worker.key ~equal:String.equal)
             ~f:(fun (target, _) ->
               List.Assoc.mem shared.persistent
                 (canonical_member shared target)
                 ~equal:String.equal))
  then State.fold terms ~init:env ~f:visit
  else State.return env

(** The instance whose history carries a fact about [field]. *)
let resolve_shared_structure ?element_type env ~at ~invariant ~field =
  let shared = env.ctx.given.shared in
  let target =
    match List.Assoc.find env.ctx.given.preds invariant ~equal:String.equal with
    | None -> invariant
    | Some (target, _) ->
        begin match
          Generic_parameters.find ~target env.ctx.given.generic_predicates invariant
        with
        | None -> canonical_member shared target
        | Some worker -> worker.name ^ "." ^ Generic_parameters.member worker
        end
  in
  let prototype =
    List.find shared.structures ~f:(fun st -> String.equal st.invariant target)
  in
  let candidates =
    match Option.bind prototype ~f:(fun st -> st.generic) with
    | None -> Option.to_list prototype
    | Some worker ->
        List.filter shared.structures ~f:(fun st ->
            Option.is_none st.generic
            && Option.exists
                 (List.Assoc.find st.context.declaration_predicates worker.key
                    ~equal:String.equal) ~f:(fun (target, _) ->
                   String.equal target st.invariant))
  in
  let candidates =
    if Option.is_none (Option.bind prototype ~f:(fun st -> st.generic)) then candidates
    else
      List.filter candidates ~f:(fun st ->
          match
            List.find st.fields ~f:(fun (name, _, _, _, _) -> String.equal name field)
          with
          | None -> false
          | Some (_, _, _, typ, _) ->
              Option.value_map element_type ~default:true ~f:(fun element_type ->
                  match Datatypes.desc env.data typ with
                  | Tconstr (_, [ element ], _) ->
                      Ctype.is_equal env.ctx.given.env false [ element ] [ element_type ]
                  | _ -> false))
  in
  match candidates with
  | [ st ] -> State.return st
  | [] ->
      State.of_result
        (error at "No instantiated invariant matches this fact about an earlier state")
  | _ :: _ :: _ ->
      State.of_result
        (error at "Several instantiated invariants match this fact about an earlier state")

(** The source types of action parameters, inferred from their atomic step patterns. *)
let action_parameter_types env (a : action) =
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
          match ctor_args with [ { term_desc = Ttuple ts; _ } ] -> ts | _ -> ctor_args
        in
        match
          find_constructor ~occurrence:t env (S.Qid (S.mk_id ~loc:pattern.term_loc c))
        with
        | Some (_, ctor) when List.length ctor.args = List.length ctor_args ->
            List.concat (List.map2_exn ctor_args ctor.args ~f:typed)
        | _ -> []
      end
    | _ -> []
  in
  match a.step with
  | Some (_, Some location :: patterns) ->
      begin match Option.map (term_type env location) ~f:(Datatypes.desc env.data) with
      | Some (Tconstr (p, [ contents ], _)) when Datatypes.is_atomic p ->
          List.concat_map patterns ~f:(function
            | Some pattern -> typed pattern contents
            | None -> [])
      | _ -> []
      end
  | _ -> []

(** The environment of an action's terms: the state [values] of [st], its parameters with
    their [bindings] and the invariant's parameters, with the values [args]. *)
let action_env ?action ctx st inv_params args values bindings =
  let ctx =
    {
      ctx with
      given =
        {
          ctx.given with
          env = st.environment;
          preds = st.context.declaration_predicates;
          spec_funcs = st.context.declaration_functions;
          proof_support = st.context.declaration_support;
        };
    }
  in
  State.map (scope_env ctx) ~f:(fun env ->
      let env = { env with vars = []; var_types = [] } in
      let env =
        bind env st.state
          (State
             (List.map2_exn st.fields values ~f:(fun (f, _, _, t, _) v -> (f, (v, t)))))
      in
      let env =
        List.fold
          (List.zip_exn inv_params (List.take args (List.length inv_params)))
          ~init:env
          ~f:(fun env ((x, t), e) ->
            { (bind env x (Value e)) with var_types = (x, t) :: env.var_types })
      in
      let param_types =
        Option.value_map action ~default:[] ~f:(action_parameter_types env)
      in
      List.fold bindings ~init:env ~f:(fun env (x, e) ->
          let env = bind env x (Value e) in
          match List.Assoc.find param_types x ~equal:String.equal with
          | None -> env
          | Some typ -> { env with var_types = (x, typ) :: env.var_types }))

(** The state after [p] of [st] from [opened], whose invariant has the parameters
    [inv_params] and the arguments [args]: each field's value, whether it changes, the
    index map of each field owned by index that it changes, as a list that it appends an
    entry to, and the entries appended, with their fields and positions. *)
let next_state ctx st ~inv_params args (opened : opened) (p : performing) =
  let open State.Syntax in
  let* env =
    action_env ~action:p.performed ctx st inv_params args opened.values p.bindings
  in
  let* next =
    State.all (List.zip_exn st.fields opened.values) ~f:(fun ((f, _, _, t, _), v) ->
        match List.Assoc.find p.performed.update f ~equal:String.equal with
        | Some term ->
            let* () =
              State.of_result
                (Source.check_logical_expression
                   ~type_variables:(source_type_variables env.ctx.given)
                   ~is_list:(is_list_term env) env.ctx.given.env
                   ~functions:(List.map env.funcs ~f:fst)
                   ~variables:(Logical_context.variables env)
                   ~expected:t term)
            in
            let* () =
              State.of_result
                (Signature_contract.terms ~expected:t ~logical_types:env.data
                   ~predicates:(fun q ->
                     Option.map
                       (List.Assoc.find env.ctx.given.preds (logical_key env q)
                          ~equal:String.equal)
                       ~f:snd)
                   ~environment:env.ctx.given.env
                   ~variables:(Logical_context.variables env)
                   [ term ])
            in
            let+ e = expected_formula env (Some t) term in
            (e, true)
        | None -> State.return (v, false))
  in
  (* An entry appended to a field owned by index, at the field's length. *)
  let appended field =
    match List.Assoc.find p.performed.update field ~equal:String.equal with
    | None -> State.return None
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
                State.map (formula env e) ~f:Option.some
            | _ -> State.return None
            end
        | _ -> State.return None
        end
  in
  let+ appended =
    State.all st.chains ~f:(fun (field, index) ->
        let i, _ =
          List.findi_exn st.fields ~f:(fun _ (f, _, _, _, _) -> String.equal f field)
        in
        let+ e = appended field in
        Option.map e ~f:(fun e ->
            let l = R.Loc.none in
            ( field,
              index,
              e,
              R.Expr.call ~loc:l
                (R.Name.make ~loc:l ~path:[ "Seq" ] "length")
                [ List.nth_exn opened.values i ] )))
  in
  let appended = List.filter_opt appended in
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
  let open State.Syntax in
  let* env = action_env ctx st st.params args values [] in
  State.all st.views ~f:(fun ((v : S.predicate), value) ->
      let inputs = List.take args (List.length v.pred_params - 1) in
      let env =
        List.fold2_exn (List.drop_last_exn v.pred_params) inputs ~init:env
          ~f:(fun env (id, _) e -> bind env id.S.pid_str (Value e))
      in
      let+ value = formula env value in
      (v.pred_name.pid_str, inputs, value))

(** What each arm of a branch starts from: the open invariants, the snapshots, the
    positions, and the atomic update's part. *)
let get_path = State.gets (fun (s : State.state) -> s.path)

let set_path path = State.modify (fun (s : State.state) -> { s with path })
let modify_path f = State.modify (fun (s : State.state) -> { s with path = f s.path })

(** That the function has an atomic update, whose part of the path is [au]. *)
let set_path_au au = modify_path (fun path -> { path with au = Some au })

(** The invariants that the function's precondition holds, with their arguments. *)
let held_invariants = State.gets (fun (s : State.state) -> s.carried.invariants)

(** Changes the atomic update's part of the path by [f]. *)
let modify_au f = modify_path (fun p -> { p with au = Option.map p.au ~f })

let put_au_state au_state = modify_au (fun au -> { au with au_state })

(** Changes the variables bound to the atomic update's results by [f]. *)
let modify_results f =
  State.modify (fun (s : State.state) ->
      {
        s with
        carried = { s.carried with au_results = Option.map s.carried.au_results ~f };
      })

(** The atomic update of the function, with its part of the path, if it has one. *)
let open_update ctx = State.gets (fun (s : State.state) -> Option.both ctx.au s.path.au)

(** [snapshots] with [state] the latest snapshot of [inv]. *)
let push_snapshot snapshots inv (state : opened) =
  ( inv,
    state :: Option.value (List.Assoc.find snapshots inv ~equal:String.equal) ~default:[]
  )
  :: List.Assoc.remove snapshots inv ~equal:String.equal

(** The contents of the atomics of the type [key_type], keys of pending calls. *)
let key_contents types ~at key_type =
  match Datatypes.desc types key_type with
  | Tconstr (path, [ contents ], _) when Datatypes.is_atomic path -> Ok contents
  | _ -> unsupported at "Helping calls waiting on a key that is not an atomic"

(** The subterms of [t] that the variables of [p] match, if [t] has its shape. *)
let rec matched_subterms (p : S.pat) (t : S.term) =
  let ( let* ) value f = Option.bind value ~f in
  match (p.pat_desc, (S.chain t).term_desc) with
  | Pwild, _ -> Some []
  | Pid id, _ -> Some [ (id.pid_str, t) ]
  | Pcast (p, _), _ -> matched_subterms p t
  | Ptuple ps, Ttuple ts when List.length ps = List.length ts ->
      let* matched =
        Option.all (List.map2_exn ps ts ~f:(fun p t -> matched_subterms p t))
      in
      Some (List.concat matched)
  | Pconstr (c, Some p), Tapply ({ term_desc = Tvar d; _ }, argument)
    when String.equal (qualid_key c) (qualid_key d) ->
      matched_subterms p argument
  | _ -> None

(** The result [h] with which an action commits the calls it helps, for the contents
    [contents] of their key after it, with its OCaml type. With [stated], the contents are
    that term in that environment, whose parts the result's pattern names. *)
let helped_value ?stated env ~at ~key_type (h : S.helped_result) contents =
  let open State.Syntax in
  let* env =
    match h.contents with
    | None -> State.return env
    | Some p ->
        let* contents_type = State.of_result (key_contents env.data ~at key_type) in
        let+ bindings =
          match
            Option.bind stated ~f:(fun (stated_env, term) ->
                Option.map (matched_subterms p term) ~f:(fun parts -> (stated_env, parts)))
          with
          | Some (stated_env, parts) ->
              State.all parts ~f:(fun (x, part) ->
                  let+ e = formula stated_env part in
                  (x, e))
          | None -> State.map ~f:snd (State.of_result (spec_pattern env p contents))
        in
        let env =
          List.fold bindings ~init:env ~f:(fun env (x, e) -> bind env x (Value e))
        in
        { env with var_types = pattern_types env p contents_type @ env.var_types }
  in
  let* typ =
    let result = Option.value (specialized_body env.ctx h.result) ~default:h.result in
    match term_type env result with
    | Some typ -> State.return typ
    | None ->
        State.of_result
          (Source.infer_logical_expression
             ~type_variables:(source_type_variables env.ctx.given)
             env.ctx.given.env ~functions:(List.map env.funcs ~f:fst)
             ~variables:(Logical_context.variables env)
             result)
  in
  let+ value = formula env h.result in
  (value, typ)

(** The lemma calls by which the action [p] that a step performs on [st], whose invariant
    has the arguments [args] and is open in [opened], helps the calls waiting in a pending
    field, committed in the state [values] after it. *)
let helping ctx st args (opened : opened) (p : performing) values ~la ~lemma =
  let open State.Syntax in
  State.map ~f:List.concat
  @@ State.all p.performed.helps ~f:(fun (field, key, (helped : S.helped_result)) ->
      let* env =
        action_env ~action:p.performed ctx st st.params args opened.values p.bindings
      in
      let* views = State.attempt (views_after ctx st args values) in
      let* c = State.attempt (formula env key) in
      (* A result carried from the key's contents: those its step writes. *)
      let+ contents =
        match (helped.contents, p.performed.step) with
        | None, _ -> State.return (Ok [])
        | Some _, Some (("compare_and_set" | "set" | "exchange"), step_args) ->
            begin match List.last step_args with
            | Some (Some written) ->
                State.map ~f:(Result.map ~f:List.return)
                  (State.attempt (formula env written))
            | _ ->
                State.of_result
                  (unsupported p.performed.action_at
                     "Helping with the contents of a key that the step writes to no \
                      given value")
            end
        | Some _, _ ->
            State.of_result
              (unsupported p.performed.action_at
                 "Helping with the contents of a key that the action's step does not \
                  write")
      in
      match
        ( List.find st.pendings ~f:(fun q -> String.equal q.pending_field field),
          Result.combine c contents ~ok:(fun c contents -> (c, contents)) ~err:Fn.const,
          views,
          List.findi st.fields ~f:(fun _ (f, _, _, _, _) -> String.equal f field) )
      with
      | Some pending, Ok (c, contents), Ok views, Some (i, _) ->
          let on = List.Assoc.find_exn opened.indices field ~equal:String.equal in
          let hc = R.Expr.var ~loc:la (name ~loc:la "hc") in
          let helped =
            R.Expr.set_compr ~loc:la
              (R.Var.make ~loc:la (ident ~loc:la "hc") (R.Type.ref ~loc:la))
              (R.Expr.binary ~loc:la Neq (R.Expr.index ~loc:la on hc) c)
          in
          [
            lemma
              (pending_name st pending "help")
              (args @ [ c ] @ contents
              @ List.map views ~f:(fun (_, _, value) -> value)
              @ [ List.nth_exn opened.values i; on; helped ]);
          ]
      | _ -> [])

(** Whether a step on atomics with contents of type [contents] may need the part [part] of
    an invariant, comparing the types' heads by name, as copies of a module have types of
    their own. *)
let part_needed types ~contents part =
  match (contents, part.part_owns) with
  | None, _ | Some _, Unknown -> true
  | Some _, Ghost -> false
  | Some contents, Atomics owned -> (
      match (Datatypes.desc types contents, Datatypes.desc types owned) with
      | Tconstr (p, _, _), Tconstr (q, _, _) -> String.equal (Path.last p) (Path.last q)
      | (Tvar _ | Tunivar _), _ | _, (Tvar _ | Tunivar _) -> true
      | Ttuple _, Ttuple _ -> true
      | _ -> false)

(** The statements closing the parts of the invariant [inv] of [st], with [args], opened
    in the state [opened], for the state [after]: unfolding those the opening did not
    unfold but whose arguments change, or that [force] says, and folding them back with
    their arguments after. *)
let reconcile_parts ?(except = fun _ -> false) st ~l ~la inv args (opened : opened)
    (after : opened) ~force =
  let open State.Syntax in
  let+ path = get_path in
  let unfolded =
    Option.value (List.Assoc.find path.unfolded inv ~equal:String.equal) ~default:[]
  in
  let before = opened_bindings st opened and after = opened_bindings st after in
  let closing =
    List.filter_map
      (List.filter st.parts ~f:(Fn.non except))
      ~f:(fun part ->
        let pred = qualified_name ~loc:l part.part_pred in
        let old_args = part_args part ~args before
        and new_args = part_args part ~args after in
        let fold = R.Stmt.fold ~loc:la pred new_args in
        if List.mem unfolded part.part_pred ~equal:String.equal then Some ([], fold)
        else if force part || not (List.equal R.Expr.alpha_equal old_args new_args) then
          Some ([ R.Stmt.unfold ~loc:l pred old_args ], fold)
        else None)
  in
  (List.concat_map closing ~f:fst, List.map closing ~f:snd)

(** The statements opening the invariants the function holds before the step at [at], on
    atomics with contents of type [contents] if given, or with [fold] closing them after
    it, where a failure is reported. *)
let performing_on (performing : performing) invariant =
  Option.value_map performing.invariant ~default:true ~f:(String.equal invariant)

let use_invariants ?performs ?(no_action = false) ?contents ctx ~(at : Location.t) ~fold =
  let open State.Syntax in
  let after = { at with loc_start = at.loc_end } in
  let l = loc at and la = loc after in
  let var x = R.Expr.var ~loc:l (name ~loc:l x) in
  let structure inv =
    List.find ctx.given.shared.structures ~f:(fun st -> String.equal st.invariant inv)
  in
  let state_value st values =
    R.Expr.call ~loc:l
      (generated_module_member ~loc:l (module_name st "state") "state")
      (grown st values)
  in
  let lemma f args =
    R.Stmt.call ~loc:l (R.Expr.call ~loc:l (qualified_name ~loc:l f) args)
  in
  let* invariants = held_invariants in
  let+ uses =
    State.all invariants ~f:(fun (inv, args) ->
        match (fold, structure inv) with
        | false, Some st ->
            (* The state, and the index maps, bound to variables. *)
            let local (raven, typ) =
              let+ x = State.fresh raven in
              (raven, x, typ)
            in
            let* locals =
              State.all st.fields ~f:(fun (_, raven, typ, _, _) -> local (raven, typ))
            in
            let* pending_locals =
              State.all st.pendings ~f:(fun p ->
                  let key =
                    Option.value
                      (Result.ok (Datatypes.typ ctx.given.types ~at p.key_type))
                      ~default:(R.Type.ref ~loc:l)
                  in
                  let+ x =
                    local (p.pending_on, R.Type.map ~loc:l (R.Type.ref ~loc:l) key)
                  in
                  (p.pending_field, x))
            in
            let* chain_locals =
              State.all st.chains ~f:(fun (field, raven) ->
                  let+ x = local (raven, chain_index_type ctx.given.types st field) in
                  (field, x))
            in
            let index_locals = chain_locals @ pending_locals in
            let state =
              {
                values = List.map locals ~f:(fun (_, x, _) -> var x);
                indices = List.map index_locals ~f:(fun (f, (_, x, _)) -> (f, var x));
              }
            in
            (* The parts of the invariant that the step may need, unfolded with it. *)
            let parts = List.filter st.parts ~f:(part_needed ctx.given.types ~contents) in
            let* () =
              modify_path (fun path ->
                  {
                    path with
                    opened =
                      (inv, state)
                      :: List.Assoc.remove path.opened inv ~equal:String.equal;
                    unfolded =
                      (inv, List.map parts ~f:(fun part -> part.part_pred))
                      :: List.Assoc.remove path.unfolded inv ~equal:String.equal;
                  })
            in
            let+ path = get_path in
            let all_locals = locals @ List.map index_locals ~f:snd in
            (* The entries of earlier snapshots are still at their positions. *)
            let current =
              state_of ~loc:l st (grown st (List.map locals ~f:(fun (_, x, _) -> var x)))
            in
            let kept =
              if has_history st then
                List.concat_map
                  (List.filter path.positions ~f:(fun p -> String.equal p.pos_inv inv))
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
            @ List.map parts ~f:(fun part ->
                R.Stmt.unfold ~loc:l
                  (qualified_name ~loc:l part.part_pred)
                  (part_args part ~args (opened_bindings st state)))
            @ kept
        | false, None ->
            State.return [ R.Stmt.unfold ~loc:l (qualified_name ~loc:l inv) args ]
        | true, _ -> (
            let definition =
              Option.to_list
                (Option.map
                   (List.Assoc.find ctx.given.shared.persistent inv ~equal:String.equal)
                   ~f:(fun def -> (def, "The invariant")))
            in
            let* () =
              State.record_origin
                {
                  at = after;
                  code = Fold;
                  message =
                    Printf.sprintf "The invariant %s may not hold after this step" inv;
                  related = definition;
                }
            in
            (* A step that performs none of the actions whose step it may be keeps the
               state as it is: its fold is at the step, with a message of its own. *)
            let* () =
              if no_action then
                State.record_origin
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
              else State.return ()
            in
            let fold ?(witnesses = []) () =
              let l = if no_action then l else la in
              [ R.Stmt.fold ~loc:l ~witnesses (qualified_name ~loc:l inv) args ]
            in
            let snapshot st (state : opened) =
              let+ () =
                modify_path (fun path ->
                    { path with snapshots = push_snapshot path.snapshots inv state })
              in
              lemma (member_name st "snapshot")
                [ List.hd_exn args; state_value st state.values ]
            in
            let* path = get_path in
            match
              (structure inv, List.Assoc.find path.opened inv ~equal:String.equal)
            with
            | Some st, Some opened ->
                let witnesses (state : opened) =
                  List.map2_exn st.fields state.values
                    ~f:(fun (_, raven, _, _, _) value -> (ident ~loc:la raven, value))
                  @ List.map st.chains ~f:(fun (field, raven) ->
                      ( ident ~loc:la raven,
                        List.Assoc.find_exn state.indices field ~equal:String.equal ))
                  @ List.map st.pendings ~f:(fun p ->
                      ( ident ~loc:la p.pending_on,
                        List.Assoc.find_exn state.indices p.pending_field
                          ~equal:String.equal ))
                in
                begin match performs with
                | Some p when performing_on p inv ->
                    (* The action's state, which the history learns if a growing field
                       changes, supplies the fold witnesses. *)
                    let* next, indices, appended =
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
                    let* () =
                      modify_path (fun path ->
                          {
                            path with
                            positions =
                              List.map appended ~f:(fun (field, e, k) ->
                                  {
                                    pos_inv = inv;
                                    pos_field = field;
                                    pos_element = e;
                                    pos_snapshot = after;
                                    pos_k = k;
                                  })
                              @ path.positions;
                          })
                    in
                    (* The registrations of the calls the action helps, carried to the
                       state after it by their transition lemmas, which commit them. *)
                    let helped part =
                      match part.part_source with
                      | `Pending field ->
                          List.find st.pendings ~f:(fun q ->
                              String.equal q.pending_field field
                              && List.exists p.performed.helps ~f:(fun (f, _, _) ->
                                  String.equal f field))
                      | `Conjunct _ -> None
                    in
                    let transited =
                      List.filter st.parts ~f:(Fn.compose Option.is_some helped)
                    in
                    let* path = get_path in
                    let unfolded =
                      Option.value
                        (List.Assoc.find path.unfolded inv ~equal:String.equal)
                        ~default:[]
                    in
                    let bindings = opened_bindings st opened in
                    let existentials =
                      List.map (invariant_existentials st) ~f:(fun x ->
                          List.Assoc.find_exn bindings x ~equal:String.equal)
                    in
                    let action_args =
                      List.map p.performed.params ~f:(fun x ->
                          List.Assoc.find_exn p.bindings x ~equal:String.equal)
                    in
                    let transitions =
                      List.concat_map transited ~f:(fun part ->
                          let pending = Option.value_exn (helped part) in
                          let pred = qualified_name ~loc:l part.part_pred in
                          (if List.mem unfolded part.part_pred ~equal:String.equal then
                             [ R.Stmt.fold ~loc:l pred (part_args part ~args bindings) ]
                           else [])
                          @ [
                              lemma
                                (transition_name st pending p.performed.action)
                                (args @ existentials @ action_args);
                            ])
                    in
                    let* unfolds, folds =
                      reconcile_parts st ~l ~la inv args opened state
                        ~except:(fun part ->
                          List.exists transited ~f:(fun t ->
                              String.equal t.part_pred part.part_pred))
                        ~force:(fun _ -> false)
                    in
                    if has_history st then
                      let+ snapshot = snapshot st state in
                      unfolds @ transitions @ learn @ (snapshot :: folds)
                      @ fold ~witnesses ()
                    else State.return (unfolds @ transitions @ folds @ fold ~witnesses ())
                | (None | Some _) when has_history st ->
                    let* _, folds =
                      reconcile_parts st ~l ~la inv args opened opened ~force:(fun _ ->
                          false)
                    in
                    let+ snapshot = snapshot st opened in
                    (snapshot :: folds) @ fold ~witnesses:(witnesses opened) ()
                | None | Some _ ->
                    (* The heap determines the state without a history. *)
                    State.return (fold ())
                end
            | _ -> State.return (fold ())))
  in
  List.concat uses

(** The known position of [e] in [field] of a snapshot of [inv]'s history among
    [positions], if any. *)
let known_position positions inv field e =
  List.find positions ~f:(fun p ->
      String.equal p.pos_inv inv
      && String.equal p.pos_field field
      && R.Expr.alpha_equal p.pos_element e)

type position_join = {
  merged : (position * R.Expr.t * R.Expr.t) list;
      (** The facts that arms learned, one for each entry, with the variables of their
          snapshots and positions. *)
  decls : R.Stmt.t list;  (** Their declarations, before the branch. *)
  learned : position list list;  (** The facts each arm learned. *)
}
(** The position facts of a branch's arms, joined after it. *)

(** Whether [p] and [q] are about the same entry. *)
let same_entry p q =
  String.equal p.pos_inv q.pos_inv
  && String.equal p.pos_field q.pos_field
  && R.Expr.alpha_equal p.pos_element q.pos_element

let empty_join = { merged = []; decls = []; learned = [] }

(** The statements at the end of an arm, which started with the facts [start], assigning
    the facts it learned to the variables of [join], with [join] after the arm. *)
let end_arm ctx join ~(start : position list) =
  let open State.Syntax in
  let l = R.Loc.none in
  let* path = get_path in
  let learned =
    List.filter path.positions ~f:(fun p -> not (List.mem start p ~equal:phys_equal))
  in
  let join = { join with learned = learned :: join.learned } in
  let+ join, assignments =
    State.fold learned ~init:(join, []) ~f:(fun (join, assignments) p ->
        let+ join, (_, snapshot, k) =
          match List.find join.merged ~f:(fun (q, _, _) -> same_entry p q) with
          | Some vars -> State.return (join, vars)
          | None ->
              let st =
                List.find_exn ctx.given.shared.structures ~f:(fun st ->
                    String.equal st.invariant p.pos_inv)
              in
              let* x = State.fresh "snapshot" in
              let+ y = State.fresh "position" in
              let decls =
                join.decls
                @ R.Stmt.local ~loc:l ~ghost:true
                    ~typ:
                      (R.Type.named ~loc:l
                         (generated_module_member ~loc:l (module_name st "state") "T")
                         [])
                    (ident ~loc:l x)
                @ R.Stmt.local ~loc:l ~ghost:true ~typ:(R.Type.int ~loc:l)
                    (ident ~loc:l y)
              in
              let vars =
                (p, R.Expr.var ~loc:l (name ~loc:l x), R.Expr.var ~loc:l (name ~loc:l y))
              in
              ({ join with decls; merged = vars :: join.merged }, vars)
        in
        ( join,
          [
            R.Stmt.assign ~loc:l [ snapshot ] (R.Stmt.expr_rhs p.pos_snapshot);
            R.Stmt.assign ~loc:l [ k ] (R.Stmt.expr_rhs p.pos_k);
          ]
          :: assignments ))
  in
  (List.concat (List.rev assignments), join)

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
  let open State.Syntax in
  let l = loc at in
  let* invariants = held_invariants in
  let+ taken =
    State.all invariants ~f:(fun (inv, args) ->
        let* path = get_path in
        match
          ( List.find ctx.given.shared.structures ~f:(fun st ->
                String.equal st.invariant inv),
            List.Assoc.find path.opened inv ~equal:String.equal )
        with
        | Some st, Some opened when has_history st ->
            let+ () =
              modify_path (fun path ->
                  { path with snapshots = push_snapshot path.snapshots inv opened })
            in
            [
              R.Stmt.call ~loc:l
                (R.Expr.call ~loc:l
                   (qualified_name ~loc:l (member_name st "snapshot"))
                   [ List.hd_exn args; state_of ~loc:l st (grown st opened.values) ]);
            ]
        | _ -> State.return [])
  in
  List.concat taken

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
  match List.Assoc.find ctx.given.shared.views pred ~equal:String.equal with
  | Some field ->
      let structure = List.hd_exn args and value = List.last_exn args in
      View_storage.write ~loc ~field (anchored ctx ~loc ~pred structure) value
      :: make ~loc ~pred p args
  | None -> make ~loc ~pred p args

let performing_updates_view ctx performing pred =
  let target key =
    canonical_member ctx.given.shared
      (Option.value_map
         (List.Assoc.find ctx.given.preds key ~equal:String.equal)
         ~default:key ~f:fst)
  in
  List.Assoc.mem ctx.given.shared.views pred ~equal:String.equal
  && List.exists ctx.given.shared.structures ~f:(fun st ->
      performing_on performing st.invariant
      && List.exists st.views ~f:(fun (view, _) ->
          String.equal (target pred) (target view.S.pred_name.pid_str)))

(** The views of the open invariants, set to their values in the states after [p], and
    folded: the views are functions of the state. *)
let perform_views ctx ~(at : Location.t) (p : performing) =
  let open State.Syntax in
  let l = loc at in
  let* path = get_path in
  let* invariants = held_invariants in
  let+ folds =
    State.all path.opened ~f:(fun (inv, opened) ->
        let structure =
          List.find ctx.given.shared.structures ~f:(fun st ->
              String.equal st.invariant inv)
        in
        let args = List.Assoc.find invariants inv ~equal:String.equal in
        match (structure, args) with
        | Some st, Some args when performing_on p inv ->
            let* next, _, _ = next_state ctx st ~inv_params:st.params args opened p in
            let+ views = views_after ctx st args (List.map next ~f:fst) in
            List.concat_map views ~f:(fun (pred, inputs, value) ->
                let raven, _ =
                  List.Assoc.find_exn ctx.given.preds pred ~equal:String.equal
                in
                with_views ctx
                  (fun ~loc ~pred:_ p args -> [ R.Stmt.fold ~loc p args ])
                  ~loc:l ~pred (qualified_name ~loc:l raven) (inputs @ [ value ]))
        | _ -> State.return [])
  in
  List.concat folds

(** The atomic that [t] denotes as the location of a step: one that an immutable record
    holds, as [q.head], or [t]'s value. *)
let atomic_of env (t : S.term) =
  let l = loc t.term_loc in
  match t.term_desc with
  | Tfield
      (({ term_desc = Tvar (Qid { pid_str = x; _ }); _ } as r), Qid { pid_str = label; _ })
    when Option.exists (List.Assoc.find env.var_types x ~equal:String.equal)
           ~f:(fun typ -> Option.is_some (atomic_in_record env.ctx typ label)) ->
      let open State.Syntax in
      let+ r = formula env r in
      R.Expr.field ~loc:l r (qualified_name ~loc:l label)
  | _ -> formula env t

(** The positions of [value], read from the atomic [atomic] at a step, in the latest
    snapshots: those of entries of fields owned by index that the invariants own the
    atomic holding. *)
let record_read ctx ~atomic value =
  let open State.Syntax in
  let* path = get_path in
  let* invariants = held_invariants in
  State.iter path.opened ~f:(fun (inv, opened) ->
      match
        ( List.find ctx.given.shared.structures ~f:(fun st ->
              String.equal st.invariant inv),
          List.Assoc.find invariants inv ~equal:String.equal,
          List.Assoc.find path.snapshots inv ~equal:String.equal )
      with
      | Some st, Some args, Some (latest :: _) when has_history st ->
          let* env = action_env ctx st st.params args opened.values [] in
          State.iter st.held ~f:(fun (location, field, position) ->
              let* k = State.attempt (formula env position) in
              let* held = State.attempt (atomic_of env location) in
              let held =
                match (held, k) with
                | Ok held, Ok k when R.Expr.alpha_equal held atomic -> Some k
                | _ -> None
              in
              match held with
              | Some k ->
                  modify_path (fun path ->
                      {
                        path with
                        positions =
                          {
                            pos_inv = inv;
                            pos_field = field;
                            pos_element = value;
                            pos_snapshot =
                              state_of ~loc:R.Loc.none st (grown st latest.values);
                            pos_k = k;
                          }
                          :: path.positions;
                      })
              | None -> State.return ())
      | _ -> State.return ())

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
  let open State.Syntax in
  let l = loc at in
  let* path = get_path in
  let* invariants = held_invariants in
  let+ performings =
    State.all path.opened ~f:(fun (inv, opened) ->
        let structure =
          List.find ctx.given.shared.structures ~f:(fun st ->
              String.equal st.invariant inv)
        in
        match (structure, List.Assoc.find invariants inv ~equal:String.equal) with
        | Some st, Some inv_args ->
            let+ performings =
              State.all st.actions ~f:(fun a ->
                  match a.step with
                  | Some (o, Some loc_pattern :: patterns)
                    when String.equal o op && List.length patterns = List.length args ->
                      let env bindings =
                        action_env ~action:a ctx st st.params inv_args opened.values
                          bindings
                      in
                      let* unbound = env [] in
                      let bindings =
                        List.concat
                          (List.map2_exn patterns args ~f:(fun p actual ->
                               match p with
                               | Some p -> bind_params unbound st opened a.params p actual
                               | None -> []))
                      in
                      let* env = env bindings in
                      let* same_field =
                        match term_type env loc_pattern with
                        | Some t ->
                            let+ f =
                              State.attempt (State.field_of_type ctx.given ~at t "")
                            in
                            begin match f with
                            | Ok (Some f) -> String.equal f field
                            | _ -> true
                            end
                        | None -> State.return true
                      in
                      let condition =
                        let contents_type =
                          Option.bind (term_type env loc_pattern) ~f:(fun typ ->
                              match Datatypes.desc env.data typ with
                              | Tconstr (path, [ contents ], _)
                                when Datatypes.is_atomic path ->
                                  Some contents
                              | _ -> None)
                        in
                        let* location_pattern = atomic_of env loc_pattern in
                        let* equalities =
                          State.all (List.zip_exn patterns args) ~f:(fun (p, actual) ->
                              match p with
                              | Some p ->
                                  let+ p = expected_formula env contents_type p in
                                  Some (R.Expr.binary ~loc:l Eq p actual)
                              | None -> State.return None)
                        in
                        (* A position that a parameter gives is within its sequence. *)
                        let+ bounds =
                          State.all (List.filter_opt patterns) ~f:(fun p ->
                              match spine (S.chain p) [] with
                              | ( { term_desc = Tvar (Qid { pid_str = "([])"; _ }); _ },
                                  [
                                    entries;
                                    ({ term_desc = Tvar (Qid { pid_str = k; _ }); _ } as i);
                                  ] )
                                when List.mem a.params k ~equal:String.equal ->
                                  let* entries = formula env entries in
                                  let+ i = formula env i in
                                  [
                                    R.Expr.binary ~loc:l Leq (R.Expr.int ~loc:l 0) i;
                                    R.Expr.binary ~loc:l Lt i
                                      (R.Expr.call ~loc:l
                                         (R.Name.make ~loc:l ~path:[ "Seq" ] "length")
                                         [ entries ]);
                                  ]
                              | _ -> State.return [])
                        in
                        List.fold
                          (List.filter_opt equalities @ List.concat bounds)
                          ~init:(R.Expr.binary ~loc:l Eq location_pattern location)
                          ~f:(R.Expr.binary ~loc:l And)
                      in
                      let+ condition = State.attempt condition in
                      begin match (same_field, condition) with
                      | true, Ok condition ->
                          Some
                            ({ performed = a; bindings; invariant = Some inv }, condition)
                      | _ -> None
                      end
                  | _ -> State.return None)
            in
            List.filter_opt performings
        | _ -> State.return [])
  in
  List.concat performings

(** The action named [a] of a structure, for [(*@ performs a *)]. *)
let named_action ctx (a : S.id) =
  let key = Option.value (ctx.given.proof_support.action_key a) ~default:a.pid_str in
  List.find_map ctx.given.shared.structures ~f:(fun st ->
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
  match
    List.find ctx.given.linearizations ~f:(fun (anchor, _) -> anchor = step_end e)
  with
  | None -> Ok None
  | Some (_, a) when ctx.given.manual ->
      error a.loc
        "Automatic linearization annotations cannot be used in a manual function proof"
  | Some (_, a) -> Result.map (Annotation.linearization a) ~f:Option.some

(** The statements committing the open update [au], opened by the step at [step], of a
    function that linearized: at once if it has no result, and otherwise at the end of the
    arm whose value is its result. *)
let commit_now (au : au) ~(step : Location.t) =
  let open State.Syntax in
  (* The commit waits for the result, or for the outcome, which a raise may decide. *)
  if au.has_result || Option.is_some au.raising then
    let+ () = put_au_state Committing in
    []
  else
    let* () = put_au_state Committed in
    au.close Commit ~value:(R.Expr.tuple ~loc:(loc step) []) ~outcome:Returned

(** The open structure with a pending field among the invariants of the function, with its
    invariant's arguments and open state; [message] at [at] if there is none. *)
let open_pending_structure ctx ~(at : Location.t) message =
  let open State.Syntax in
  let* path = get_path in
  let* invariants = held_invariants in
  match
    List.find_map path.opened ~f:(fun (inv, opened) ->
        match
          ( List.find ctx.given.shared.structures ~f:(fun st ->
                String.equal st.invariant inv),
            List.Assoc.find invariants inv ~equal:String.equal )
        with
        | Some st, Some args when not (List.is_empty st.pendings) ->
            Some (st, args, opened)
        | _ -> None)
  with
  | Some found -> State.return found
  | None -> State.of_result (error at message)

(** The environment of a decision at a step whose result [value] matches [p], in the state
    [opened] of [st]. *)
let decision_env ?value_type ctx st (opened : opened) (p : S.pat) value =
  let open State.Syntax in
  let* env = scope_env ctx in
  let env =
    bind env st.state
      (State
         (List.map2_exn st.fields opened.values ~f:(fun (f, _, _, t, _) v -> (f, (v, t)))))
  in
  match p.pat_desc with
  | Pid x ->
      let env = bind env x.pid_str (Value value) in
      State.return
        (Option.value_map value_type ~default:env ~f:(fun ty ->
             { env with var_types = (x.pid_str, ty) :: env.var_types }))
  | Pwild -> State.return env
  | _ ->
      State.of_result
        (unsupported p.pat_loc "A pattern other than a variable, before a choice,")

(** The statements of the step at [at] of the function with the update [au], whose result
    [value] matches [p]: the invariants are open, and [outcome] linearizes the function or
    leaves it to be helped, registered on a pending field. *)
let decide ?value_type ctx (au : au) ~(at : Location.t) ~value (p : S.pat)
    (outcome : S.outcome) =
  let open State.Syntax in
  let l = loc at in
  let var x = R.Expr.var ~loc:l (name ~loc:l x) in
  let* st, args, opened =
    open_pending_structure ctx ~at
      "A step that may wait without a structure with pending calls"
  in
  let* env = decision_env ?value_type ctx st opened p value in
  let* start = get_path in
  let snapshots = start.snapshots in
  let* hc = State.fresh "registration" in
  let* registered = State.fresh "registered" in
  let* waiting = State.fresh "waiting" in
  (* The pending field the call may wait in. *)
  let rec waits (o : S.outcome) =
    match o with
    | Waits (field, _) -> Some field
    | Chooses (_, a, b) -> Option.first_some (waits a) (waits b)
    | Commits | Commits_with _ -> None
  in
  let* pending =
    State.of_result
      begin match
        Option.map (waits outcome) ~f:(fun (field : S.term) -> field.term_desc)
      with
      | Some (Tfield (_, Qid f)) ->
          (* A copy for a witness's constructor waits in the field of its calls. *)
          let field =
            match ctx.given.specialized_witness with
            | Some (_, ctor)
              when List.exists st.pendings ~f:(fun q ->
                       String.equal q.pending_field (f.pid_str ^ "$" ^ ctor)) ->
                f.pid_str ^ "$" ^ ctor
            | _ -> f.pid_str
          in
          begin match
            List.find st.pendings ~f:(fun q -> String.equal q.pending_field field)
          with
          | Some q -> Ok q
          | None ->
              error at (Printf.sprintf "%s is not a field of pending calls" f.pid_str)
          end
      | Some _ ->
          error at "A field of pending calls of the state, as s.waiting, to wait in"
      | None -> error at "A choice that never waits"
      end
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
        let* fold = use_invariants ctx ~at ~fold:true in
        let+ () = modify_path (fun path -> { path with snapshots }) in
        commit @ fold @ ends registrations false
    | Commits ->
        State.of_result
          (unsupported at "Linearizing with the function's result, before a choice,")
    | Waits (_, key) ->
        let* key = formula env key in
        (* A carried result, unknown until helped. *)
        let _, _, helped_result = pending.helping in
        let* stored =
          match helped_result.contents with
          | None -> State.return None
          | Some _ ->
              let* _, result_type =
                helped_value env ~at ~key_type:pending.key_type helped_result key
              in
              let* typ = State.typ ctx ~at result_type in
              let+ x = State.fresh "result" in
              Some (x, typ)
        in
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
        let registered_on = R.Expr.update ~loc:l on (var hc) key in
        let* unfolds, folds =
          reconcile_parts st ~l ~la:(loc after) inv args opened
            {
              values = next;
              indices =
                List.map opened.indices ~f:(fun (field, e) ->
                    ( field,
                      if String.equal field pending.pending_field then registered_on
                      else e ));
            }
            ~force:(fun _ -> false)
        in
        let+ () =
          State.record_origin
            {
              at = after;
              code = Fold;
              message = Printf.sprintf "The invariant %s may not hold after this step" inv;
              related = [];
            }
        in
        let _, raven_field, _, _, _ = List.nth_exn st.fields i in
        unfolds
        @ Option.value_map stored ~default:[] ~f:(fun (x, typ) ->
            R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x))
        @ [
            R.Stmt.assign ~loc:l
              [ var hc ]
              (R.Stmt.new_rhs
                 ([
                    (field "watched", Some key);
                    (field "linked", Some (R.Expr.bool ~loc:l false));
                    (field "token", Some au.token);
                    (field "retired", Some (R.Expr.bool ~loc:l false));
                  ]
                 @ Option.value_map stored ~default:[] ~f:(fun (x, _) ->
                     [ (field "result", Some (var x)) ])));
            R.Stmt.fold ~loc:l
              ~witnesses:
                ([
                   (ident ~loc:l "tok", au.token);
                   (ident ~loc:l "l", R.Expr.bool ~loc:l false);
                   (ident ~loc:l "r", R.Expr.bool ~loc:l false);
                 ]
                @ Option.value_map stored ~default:[] ~f:(fun (x, _) ->
                    [ (ident ~loc:l "res", var x) ]))
              (qualified_name ~loc:l (pending_name st pending "registration"))
              (var hc :: args);
            lemma (member_name st "learn")
              [ List.hd_exn args; state opened.values; state next ];
            lemma (member_name st "snapshot") [ List.hd_exn args; state next ];
          ]
        @ folds
        @ [
            R.Stmt.fold ~loc:(loc after)
              ~witnesses:
                [
                  (ident ~loc:l raven_field, added);
                  (ident ~loc:l pending.pending_on, registered_on);
                ]
              (qualified_name ~loc:l inv) args;
          ]
        @ ends added true
    | Chooses (c, a, b) ->
        let* c = formula env c in
        let* a = arm a in
        let+ b = arm b in
        [ R.Stmt.if_ ~loc:l c a b ]
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
  let registration =
    Registered
      {
        registration = var hc;
        registered = var registered;
        pending_inv = st.invariant;
        pending;
      }
  in
  let+ () =
    modify_path (fun path ->
        {
          path with
          snapshots = push_snapshot snapshots st.invariant merged;
          au =
            Option.map path.au ~f:(fun au ->
                { au with au_state = registration; au_step = at });
        })
  in
  let local x typ = R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x) in
  let _, _, waiting_typ, _, _ = List.nth_exn st.fields j in
  local hc (R.Type.ref ~loc:l)
  @ local registered (R.Type.bool ~loc:l)
  @ local waiting waiting_typ
  @ [ R.Stmt.ghost_block ~loc:l stmts ]

(** Whether a step's result [value] matches [p], and [result], in the scope of [ctx]. *)
let collected_terms ctx (p : S.pat) value result =
  let open State.Syntax in
  let* env = scope_env ctx in
  let* matches, _ = State.of_result (spec_pattern env p value) in
  let+ result = formula env result in
  (matches, result)

(** The ghost statements retiring the registration of the function with the update [au],
    left to be helped as [r] says, at the step at [at] whose result is [value], after
    [commit], with the registration unfolded. *)
let retire ctx (au : au) (r : registered) ~(at : Location.t) ~value commit =
  let open State.Syntax in
  let l = loc at in
  let var x = R.Expr.var ~loc:l (name ~loc:l x) in
  let* st, args, _ =
    open_pending_structure ctx ~at
      "A step that collects a result without a structure with pending calls"
  in
  let* linked = State.fresh "linked" in
  (* A carried result, kept as the registration holds it. *)
  let _, _, helped_result = r.pending.helping in
  let+ stored =
    match helped_result.contents with
    | None -> State.return None
    | Some _ ->
        let* env = scope_env ctx in
        let* _, result_type =
          helped_value env ~at ~key_type:r.pending.key_type helped_result value
        in
        let* typ = State.typ ctx ~at result_type in
        let+ x = State.fresh "result" in
        Some (x, typ)
  in
  let carried f = Option.value_map stored ~default:[] ~f in
  let registration = qualified_name ~loc:l (pending_name st r.pending "registration") in
  let retired = qualified_name ~loc:l (pending_name st r.pending "retired") in
  [
    R.Stmt.if_ ~loc:l r.registered
      (R.Stmt.local ~loc:l ~ghost:true ~typ:(R.Type.bool ~loc:l) (ident ~loc:l linked)
      @ carried (fun (x, typ) -> R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x))
      @ [
          R.Stmt.unfold ~loc:l
            ~witnesses:
              ((ident ~loc:l linked, var "l")
              :: carried (fun (x, _) -> [ (ident ~loc:l x, var "res") ]))
            registration (r.registration :: args);
        ]
      @ commit
      @ [
          R.Stmt.assign ~loc:l
            [ R.Expr.field ~loc:l r.registration retired ]
            (R.Stmt.expr_rhs (R.Expr.bool ~loc:l true));
          R.Stmt.fold ~loc:l
            ~witnesses:
              ([
                 (ident ~loc:l "tok", au.token);
                 (ident ~loc:l "l", var linked);
                 (ident ~loc:l "r", R.Expr.bool ~loc:l true);
               ]
              @ carried (fun (x, _) -> [ (ident ~loc:l "res", var x) ]))
            registration (r.registration :: args);
        ])
      [];
  ]

(** The statements of the step at [at] that collects the result of the function with the
    update [au], left to be helped as [r] says, if its result [value] matches [p]:
    committing with [result] if nobody helped it, and retiring the registration. *)
let collect ctx (au : au) (r : registered) ~(at : Location.t) ~value (p : S.pat) result =
  let open State.Syntax in
  let l = loc at in
  let* matches, result = collected_terms ctx p value result in
  let* commit = au.commit_only ~at ~value:result in
  let commit =
    match matches with Some c -> [ R.Stmt.if_ ~loc:l c commit [] ] | None -> commit
  in
  let* retiring = retire ctx au r ~at ~value commit in
  let+ () = modify_au (fun au -> { au with au_state = Committed; au_step = at }) in
  [ R.Stmt.ghost_block ~loc:l retiring ]

(** The statements of the read at [at] that collects the result of the function with the
    update [au], left to be helped as [r] says, whose result [value] has the constructor
    [c] if nobody helped it: retiring the registration, the invariants left open for the
    arm of that constructor, which opens the update and commits with the function's
    result. *)
let collect_returning ctx (au : au) (r : registered) ~(at : Location.t) ~value c =
  let open State.Syntax in
  let l = loc at in
  let* retiring = retire ctx au r ~at ~value [] in
  let+ () = modify_au (fun au -> { au with au_state = Collecting c; au_step = at }) in
  [ R.Stmt.ghost_block ~loc:l retiring ]

(** The statements of [access], an atomic step, inside the atomic update of a function
    with an atomic contract that has not linearized yet. The step linearizes the function
    as [how] says: always, never, if it is a [compare_and_set] that succeeds, or if it is
    a read whose value has a constructor. *)
let linearize ?step ?value ?access_type ?contents ctx ~at
    (how :
      [ `Commit | `Abort | `Cas | `Returning of string | `Decide of S.pat * S.outcome ])
    access =
  let open State.Syntax in
  let annotation =
    List.Assoc.find ctx.given.access_proofs
      (at.Location.loc_start.pos_cnum, at.loc_end.pos_cnum)
      ~equal:Poly.equal
  in
  if ctx.given.manual then
    match (annotation, value, access_type) with
    | None, _, _ -> State.return access
    | Some annotation, Some result, Some result_type ->
        State.map ~f:fst
          (access_proof ctx annotation ~result_type (fun _ ->
               State.return (access, result, [])))
    | Some annotation, _, _ ->
        State.of_result
          (error annotation.loc "This operation does not support an access proof")
  else if Option.is_some annotation then
    State.of_result
      (error (Option.value_exn annotation).loc
         "Ghost.scope requires a manual function proof")
  else
    let l = loc at in
    (* The actions that the step may perform, once the invariants are open. *)
    let performings () =
      match step with
      | Some (op, field, location, args, _) ->
          step_performings ctx ~at ~op ~field ~location args
      | None -> State.return []
    in
    let around access =
      let* opening = use_invariants ?contents ctx ~at ~fold:false in
      let* performings = performings () in
      match (performings, step) with
      | [], _ | _, None ->
          let+ closing = use_invariants ctx ~at ~fold:true in
          opening @ access @ closing
      | performings, Some (_, _, _, _, result) ->
          (* If the step succeeds, it performs the action whose step it is, or changes
           nothing. The state before it is the latest snapshot after it on every path. *)
          let* snapshot = take_snapshots ctx ~at in
          let* start = get_path in
          let reset =
            modify_path (fun path -> { path with snapshots = start.snapshots })
          in
          let close ?performs ?no_action () =
            let* () = reset in
            use_invariants ?performs ?no_action ctx ~at ~fold:true
          in
          let* unchanged = close ~no_action:true () in
          let* performed =
            State.fold (List.rev performings) ~init:unchanged
              ~f:(fun rest (p, condition) ->
                let+ closed = close ~performs:p () in
                [ R.Stmt.if_ ~loc:l condition closed rest ])
          in
          let* failed = close () in
          let+ () = reset in
          opening @ access @ snapshot
          @ [ R.Stmt.if_ ~loc:l result [ R.Stmt.ghost_block ~loc:l performed ] failed ]
    in
    let* update = open_update ctx in
    match (update, how, value) with
    | None, `Decide _, _ ->
        State.of_result
          (error at "A choice of how to linearize outside an atomic function")
    | Some (au, au_path), `Decide (p, o), Some value ->
        begin match (au_path.au_state, o) with
        | Pending, _ ->
            (* The invariants open, the update not: the step decides. *)
            let* opening = use_invariants ctx ~at ~fold:false in
            let+ decision = decide ?value_type:access_type ctx au ~at ~value p o in
            opening @ access @ decision
        | Registered r, Commits_with result ->
            let* opening = use_invariants ctx ~at ~fold:false in
            let* collected = collect ctx au r ~at ~value p result in
            let+ closing = use_invariants ctx ~at ~fold:true in
            opening @ access @ collected @ closing
        | _ ->
            State.of_result
              (error at
                 "Caravan cannot tell whether the function has linearized before this \
                  step")
        end
    | Some _, `Decide _, None ->
        State.of_result (error at "Only a read can linearize by its value")
    | None, _, _ -> around access
    | Some (au, au_path), ((`Commit | `Abort | `Cas | `Returning _) as how), _ ->
        begin match au_path.au_state with
        | Committed -> around access
        | Registered r ->
            begin match (how, value) with
            | `Returning c, Some value ->
                let* opening = use_invariants ctx ~at ~fold:false in
                let+ collected = collect_returning ctx au r ~at ~value c in
                opening @ access @ collected
            | _ ->
                State.of_result
                  (error at
                     "This function waits to be helped: the next step collects its \
                      result, as (*@ returning Nil -> commit true *)")
            end
        | Committing | On_cas | On_read _ | Collecting _ | Partly | Unknown ->
            State.of_result
              (error at
                 "Caravan cannot tell whether the function has linearized before this \
                  step")
        | Pending ->
            let* opening, values =
              au.open_ ~invariants_open:false ~contents ~at ~unfold:true
            in
            let* () =
              modify_au (fun au -> { au with au_values = values; au_step = at })
            in
            let* () =
              modify_results (fun results -> { results with read_results = [] })
            in
            let+ closing =
              match how with
              | `Abort ->
                  let* () = put_au_state Pending in
                  au.close Abort ~value:(R.Expr.tuple ~loc:(loc at) []) ~outcome:Returned
              | `Commit -> commit_now au ~step:at
              | `Cas ->
                  let* () = put_au_state On_cas in
                  (* The action that the step performs if it succeeds, which linearizes the
                   function. *)
                  let* performings = performings () in
                  let linearizing =
                    List.filter performings ~f:(fun (p, _) ->
                        List.mem p.performed.linearizes au.role ~equal:Ident.same)
                  in
                  let* path = get_path in
                  begin match
                    (linearizing, Option.bind path.au ~f:(fun au -> au.au_performing))
                  with
                  | _, Some (selected, None) ->
                      begin match
                        List.find performings ~f:(fun (p, _) ->
                            String.equal p.performed.action selected.performed.action)
                      with
                      | None -> State.return []
                      | Some (p, condition) ->
                          let+ () =
                            modify_au (fun au ->
                                { au with au_performing = Some (p, Some condition) })
                          in
                          []
                      end
                  | _, Some (_, Some _) | [], None -> State.return []
                  | [ (p, condition) ], None ->
                      let+ () =
                        modify_au (fun au ->
                            { au with au_performing = Some (p, Some condition) })
                      in
                      []
                  | _ :: _ :: _, None ->
                      State.of_result
                        (error at
                           "This step may perform several actions that linearize the \
                            function")
                  end
              | `Returning c ->
                  let+ () = put_au_state (On_read c) in
                  []
            in
            opening @ access @ closing
        end

(** The statements opening the update [au] for a call at [at] that linearizes the function
    in its place, and the values of the implicit parameters in the update, if the function
    has not linearized yet. *)
let open_for_call (au : au) ~(at : Location.t) =
  let open State.Syntax in
  let* path = get_path in
  match Option.map path.au ~f:(fun au -> au.au_state) with
  | Some Pending ->
      let* opening, values =
        au.open_ ~invariants_open:false ~contents:None ~at ~unfold:false
      in
      let+ () =
        modify_au (fun au ->
            { au with au_values = values; au_step = at; au_state = Committed })
      in
      Some (opening, values)
  | None | Some Committed -> State.return None
  | Some (Committing | On_cas | On_read _ | Collecting _ | Partly | Registered _ | Unknown)
    ->
      State.of_result
        (error at
           "Caravan cannot tell whether the function has linearized before this call")

(** That the step that opens the update performs [performed], as [(*@ performs pop *)]
    says. *)
let set_performing performed =
  modify_au (fun au ->
      {
        au with
        au_performing = Some ({ performed; bindings = []; invariant = None }, None);
      })

(** That the variable [id] is bound to the result of a [compare_and_set], or to its
    negation if not [polarity]. *)
let record_cas_result (id : Ident.t) polarity =
  modify_results (fun results ->
      {
        results with
        cas_results = (Ident.unique_name id, polarity) :: results.cas_results;
      })

(** That the variable [id] is bound to the value of the last read. *)
let record_read_result (id : Ident.t) =
  modify_results (fun results ->
      { results with read_results = Ident.unique_name id :: results.read_results })

(** The statements at the start of an arm of a branch on the result of the step that left
    the update open: committing if the step linearized the function there, as [commits]
    says, and aborting otherwise. *)
let enter_arm ctx ~(commits : bool option) =
  let open State.Syntax in
  let* update = open_update ctx in
  match update with
  | Some (au, ({ au_state = On_cas | On_read _; _ } as au_path)) ->
      begin match commits with
      | Some true -> commit_now au ~step:au_path.au_step
      | Some false ->
          let* () = put_au_state Pending in
          au.close Abort
            ~value:(R.Expr.tuple ~loc:(loc au_path.au_step) [])
            ~outcome:Returned
      | None ->
          let+ () = put_au_state Unknown in
          []
      end
  | Some (au, ({ au_state = Collecting _; _ } as au_path)) ->
      begin match commits with
      | Some true ->
          let at = au_path.au_step in
          let* opening, values =
            au.open_ ~invariants_open:true ~contents:None ~at ~unfold:true
          in
          let* () = modify_au (fun au -> { au with au_values = values }) in
          let+ commit = commit_now au ~step:at in
          opening @ commit
      | Some false ->
          (* Helped: committed by the helping call, the invariants open since the read. *)
          let* () = put_au_state Committed in
          use_invariants ctx ~at:au_path.au_step ~fold:true
      | None ->
          let+ () = put_au_state Unknown in
          []
      end
  | _ -> State.return []

(** The statements at the end of an arm whose value [v] is the function's result: the
    commit, if the function linearized in the arm. *)
let finish_arm ctx ~tail v =
  let open State.Syntax in
  let* update = open_update ctx in
  match update with
  | Some (au, { au_state = Committing; _ }) when tail ->
      let* () = put_au_state Committed in
      au.close Commit ~value:v ~outcome:Returned
  | _ -> State.return []

(** The state of the atomic update after two branches. *)
let join_au a b =
  match (a, b) with
  | _ when Poly.equal a b -> a
  | (Pending | Committed | Partly), (Pending | Committed | Partly) -> Partly
  | _ -> Unknown

let au_state =
  State.gets (fun (s : State.state) -> Option.map s.path.au ~f:(fun au -> au.au_state))

let set_au_state = function Some state -> put_au_state state | None -> State.return ()

(** Whether [c] is the result of a [compare_and_set], [Some false] if its negation. *)
let cas_polarity (c : Typedtree.expression) =
  State.gets (fun (s : State.state) ->
      let rec polarity (c : Typedtree.expression) =
        match c.exp_desc with
        | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, args) ->
            begin match (atomic_name path, unop_of_path path, args) with
            | Some "compare_and_set", _, _ -> Some true
            | _, Some `Not, [ (_, Arg a) ] -> Option.map (polarity a) ~f:not
            | _ -> None
            end
        | Texp_ident (Pident id, _, _) ->
            Option.bind s.carried.au_results ~f:(fun results ->
                List.Assoc.find results.cas_results (Ident.unique_name id)
                  ~equal:String.equal)
        | _ -> None
      in
      polarity c)

(** Whether [e] is the value of the last read. *)
let is_read_value (e : Typedtree.expression) =
  State.gets (fun (s : State.state) ->
      match e.exp_desc with
      | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _) ->
          Option.equal String.equal (atomic_name path) (Some "get")
      | Texp_ident (Pident id, _, _) ->
          Option.exists s.carried.au_results ~f:(fun results ->
              List.mem results.read_results (Ident.unique_name id) ~equal:String.equal)
      | _ -> false)

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

let no_loop_before_linearizing ~at =
  let open State.Syntax in
  let* state = au_state in
  match state with
  | None | Some Committed -> State.return ()
  | Some _ ->
      State.of_result
        (unsupported at
           "A loop in a function with an atomic contract, before it linearizes,")

(** The ghost fields attached to these source allocation tags, with their initial values.
    A view's value is set when its invariant is established. *)
let view_allocation ctx ~loc:l (tags : string list) =
  let open State.Syntax in
  let views =
    List.concat_map tags ~f:(fun tag ->
        Option.value
          (List.Assoc.find ctx.given.shared.anchors tag ~equal:String.equal)
          ~default:[])
  in
  let+ allocated =
    State.all views ~f:(fun (view, init) ->
        match init with
        | Fixed init -> State.return ([], (qualified_name ~loc:l view, Some init))
        | Snapshot typ ->
            let+ x = State.fresh "view" in
            ( R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x),
              ( qualified_name ~loc:l view,
                Some
                  (View_storage.chunk ~loc:l ~field:view
                     (R.Expr.var ~loc:l (name ~loc:l x))
                     1.0) ) ))
  in
  (List.concat_map allocated ~f:fst, List.map allocated ~f:snd)

(** The ghost initializers that the annotation on the allocation [e] gives, if any. *)
let allocation_initializers ctx (e : Typedtree.expression) =
  let open State.Syntax in
  match
    List.Assoc.find ctx.given.initializations
      (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum)
      ~equal:Poly.equal
  with
  | None -> State.return []
  | Some annotation ->
      let* initializers = State.of_result (Annotation.initializes annotation) in
      let* env = scope_env ctx in
      ghost_initializers env ~owner:e.exp_type initializers
