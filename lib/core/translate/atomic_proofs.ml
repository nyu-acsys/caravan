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
      Option.map (Datatypes.cell_name ~prefix:"atomic_" ~suffix:"" types elt)
        ~f:(fun field -> (field, itself))
  | Tconstr (p, [ elt ], _) when Datatypes.is_ref p ->
      Option.map (Datatypes.cell_name ~prefix:"ref_" ~suffix:"_contents" types elt)
        ~f:(fun field -> (field, itself))
  | Tconstr (p, [], _) ->
      begin match Datatypes.find types p with
      | Some { heap = Some (f :: _); _ } -> Some (f.raven_field, itself)
      | Some { heap = None; ctors = [ { ocaml = ""; fields; args; _ } ]; _ } ->
          List.find_map (List.zip_exn fields args) ~f:(fun (label, a) ->
              match Datatypes.desc types a with
              | Tconstr (q, [ elt ], _) when Datatypes.is_atomic q ->
                  Option.map (Datatypes.cell_name ~prefix:"atomic_" ~suffix:"" types elt)
                    ~f:(fun field ->
                      ( field,
                        fun ~loc e -> R.Expr.field ~loc e (qualified_name ~loc label) ))
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
