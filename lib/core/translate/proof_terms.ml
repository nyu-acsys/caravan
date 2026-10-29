(** Ghost code: lemma and predicate calls, proof expressions, and access and return
    proofs. *)

open Base
open Translate_context
open Spec_terms

(** The latest binding of each variable in scope. *)
let scope ctx =
  List.fold (List.rev ctx.procedure.names.scope) ~init:[] ~f:(fun acc (x, b) ->
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
    data = ctx.given.types;
    funcs = ctx.given.spec_funcs;
    vars = List.map scope ~f:(fun (x, (raven, _)) -> (x, Raven raven));
  }

(** A call of a checked proof lemma, separate from logical function applications. *)
let lemma_call env (t : S.term) =
  let head, args = spine t [] in
  match head.term_desc with
  | Tvar (Qid id) when List.Assoc.mem env.vars id.pid_str ~equal:String.equal ->
      error id.pid_loc "A local proof value cannot be called as a lemma"
  | Tvar q ->
      let display = qualid_key q in
      begin match
        List.Assoc.find env.ctx.given.proof_lemmas (logical_key env q) ~equal:String.equal
      with
      | None -> error head.term_loc (Printf.sprintf "Unknown lemma %s" display)
      | Some signature ->
          let maximum = List.length signature.lemma_inputs in
          let minimum = maximum - signature.lemma_implicit_count in
          let arity = List.length args in
          if arity < minimum || arity > maximum then
            error t.term_loc
              (if minimum = maximum then
                 Printf.sprintf "Lemma %s expects %d arguments" display maximum
               else
                 Printf.sprintf "Lemma %s expects between %d and %d arguments" display
                   minimum maximum)
          else
            let* args =
              typed_arguments env ~at:t.term_loc
                (List.take signature.lemma_inputs arity)
                args
            in
            Ok
              ( R.Expr.call ~loc:(loc t.term_loc)
                  (qualified_name ~loc:(loc t.term_loc) signature.lemma_raven)
                  args,
                signature.lemma_outputs )
      end
  | _ -> error t.term_loc "Expected a lemma applied to its arguments"

let predicate_use env ~unfold t witnesses make =
  let head, args = spine t [] in
  match head.term_desc with
  | Tvar q when List.Assoc.mem env.ctx.given.preds (logical_key env q) ~equal:String.equal
    ->
      let key = logical_key env q in
      let* () =
        if List.mem env.ctx.given.proof_support.opaque_predicates key ~equal:String.equal
        then
          error head.term_loc
            "The definition of this predicate is hidden by its module signature"
        else Ok ()
      in
      let raven, types =
        List.Assoc.find_exn env.ctx.given.preds key ~equal:String.equal
      in
      let* args =
        predicate_arguments env ~at:t.term_loc ~display:(qualid_key q) key types args
      in
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
      Ok (make ~loc:l ?witnesses:(Some witnesses) (qualified_name ~loc:l raven) args)
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

let atomic_proof_signature env t =
  let head, _ = spine t [] in
  match head.S.term_desc with
  | Tvar q ->
      Option.bind (atomic_method env q) ~f:(fun (signature, method_) ->
          if List.mem [ "bind"; "access"; "abort"; "commit" ] method_ ~equal:String.equal
          then
            Option.map (atomic_inputs signature method_) ~f:(fun (inputs, outputs) ->
                {
                  lemma_raven = qualid_key q;
                  lemma_constant = false;
                  lemma_inputs = inputs;
                  lemma_implicit_count = 0;
                  lemma_outputs = outputs;
                })
          else None)
  | _ -> None

let proof_call env t =
  let head, args = spine t [] in
  match head.S.term_desc with
  | Tvar q when Option.is_some (atomic_proof_signature env t) ->
      let signature, method_ = Option.value_exn (atomic_method env q) in
      let inputs, outputs = Option.value_exn (atomic_inputs signature method_) in
      let* values = typed_arguments env ~at:t.term_loc inputs args in
      let* () =
        if
          String.equal method_ "bind"
          && not
               (Option.equal String.equal env.ctx.given.current_procedure
                  (Some signature.au_procedure))
        then error t.term_loc "An AU token can only be bound in its own procedure"
        else Ok ()
      in
      let l = loc t.term_loc in
      let values =
        if String.equal method_ "bind" then []
        else atomic_arguments ~loc:l signature method_ values
      in
      let method_ =
        match method_ with
        | "bind" -> "bindAU"
        | "access" -> "openAU"
        | "abort" -> "abortAU"
        | "commit" -> "commitAU"
        | _ -> method_
      in
      Ok (R.Expr.call ~loc:l (name ~loc:l method_) values, outputs)
  | _ -> lemma_call env t

let proof_signature env (t : S.term) =
  let head, _ = spine t [] in
  match atomic_proof_signature env t with
  | Some _ as signature -> signature
  | None ->
      begin match head.term_desc with
      | Tvar (Qid id) when List.Assoc.mem env.vars id.pid_str ~equal:String.equal -> None
      | Tvar q ->
          List.Assoc.find env.ctx.given.proof_lemmas (logical_key env q)
            ~equal:String.equal
      | _ -> None
      end

let ghost_fpu env t =
  let _, args = spine t [] in
  match args with
  | [ location; before; after ] ->
      begin match ghost_projection env location with
      | None -> error location.term_loc "Ghost.fpu needs a declared ghost field location"
      | Some (field, _) ->
          let* () =
            if resource_field env field then Ok ()
            else error t.term_loc "Ghost.fpu requires a resource field"
          in
          let* location = location_of env location in
          let value t =
            let* () =
              match term_type env t with
              | Some actual
                when not
                       (Ctype.is_equal env.ctx.given.env false [ field.field_value ]
                          [ actual ]) ->
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

(** Initializers are attached only to fresh allocations. *)
let ghost_initializers env ~owner t =
  let* entries =
    match list_literal t with
    | Some entries -> Ok entries
    | None -> error t.S.term_loc "Ghost initializers must be a list literal"
  in
  let* fields =
    all entries ~f:(fun entry ->
        match spine entry [] with
        | { term_desc = Tvar (Qdot (Qid m, op)); _ }, [ { term_desc = Tvar q; _ }; value ]
          when String.equal m.pid_str "Ghost" && String.equal op.pid_str "init" ->
            let at = S.qualid_loc q in
            begin match ghost_descriptor env q with
            | None -> error at "Unknown ghost field"
            | Some _ when shadowed_ghost_descriptor env q ->
                error at "This name shadows a ghost field descriptor"
            | Some field ->
                let* () =
                  if
                    Ctype.is_equal env.ctx.given.env false [ owner ] [ field.field_owner ]
                  then Ok ()
                  else error at "This ghost field has a different owner type"
                in
                let* () =
                  Source.check_logical_expression env.ctx.given.env
                    ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types
                    ~expected:field.field_value value
                in
                let* value = expected_formula env (Some field.field_value) value in
                Ok
                  ( ghost_field_name field,
                    ( qualified_name ~loc:(loc entry.term_loc) (ghost_field_name field),
                      Some value ) )
            end
        | _ -> error entry.term_loc "Expected Ghost.init field value")
  in
  let* () =
    match List.find_a_dup (List.map fields ~f:fst) ~compare:String.compare with
    | None -> Ok ()
    | Some _ -> error t.term_loc "A ghost field is initialized more than once"
  in
  Ok (List.map fields ~f:snd)

let ghost_value_location env t =
  match ghost_projection env t with
  | None -> error t.S.term_loc "Expected a declared ghost field location"
  | Some (field, _) when resource_field env field ->
      error t.term_loc "Ghost.read and Ghost.write require an ordinary value field"
  | Some (field, _) ->
      let* location = location_of env t in
      Ok (field, location)

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
  match (ghost_operation t, snd (spine t [])) with
  | Some "alloc", [ _ ] ->
      Result.map (Source.ghost_type env.ctx.given.env ~at:t.term_loc) ~f:Option.some
  | Some "read", [ location ] ->
      let* field, _ = ghost_value_location env location in
      Ok (Some field.field_value)
  | _ -> (
      match t.term_desc with
      | Tcast (_, ty) ->
          let* ty = Source.ocaml_type env.ctx.given.env ~at:t.term_loc ty in
          Ok (Some ty)
      | Tconst (Pconst_integer _) -> Ok (Some Predef.type_int)
      | Ttrue | Tfalse -> Ok (Some Predef.type_bool)
      | Tapply ({ term_desc = Tvar (Qid { pid_str = "Some"; _ }); _ }, value) ->
          let* ty = proof_value_type env value in
          Ok (Option.map ty ~f:(fun ty -> Ctype.newconstr Predef.path_option [ ty ]))
      | Ttuple [] -> Ok (Some Predef.type_unit)
      | Ttuple ts ->
          let* ts = all ts ~f:(proof_value_type env) in
          Ok
            (Option.map (Option.all ts) ~f:(fun ts ->
                 Btype.newgenty (Ttuple (List.map ts ~f:(fun ty -> (None, ty))))))
      | _ -> (
          match term_type env t with
          | Some ty -> Ok (Some ty)
          | None ->
              Result.map
                (Source.infer_logical_expression env.ctx.given.env
                   ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types t)
                ~f:Option.some))

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
              let* ty = Source.ocaml_type env.ctx.given.env ~at:p.pat_loc ty in
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

let proof_state ctx ~at =
  Option.value ctx.procedure.proof_state
    ~default:(unit_value ~loc:(loc at), Predef.type_unit)

let rec proof_pattern env (pattern : S.pat) ty value =
  match pattern.pat_desc with
  | Pwild -> Ok env
  | Pid id ->
      Ok
        {
          (bind env id.pid_str (Value value)) with
          var_types = (id.pid_str, ty) :: env.var_types;
        }
  | Pcast (pattern, annotation) ->
      let* expected =
        Source.ocaml_type env.ctx.given.env ~at:pattern.pat_loc annotation
      in
      if Ctype.is_equal env.ctx.given.env false [ expected ] [ ty ] then
        proof_pattern env pattern ty value
      else error pattern.pat_loc "The proof pattern has a different type from its input"
  | Ptuple [] when Ctype.is_equal env.ctx.given.env false [ ty ] [ Predef.type_unit ] ->
      Ok env
  | Ptuple patterns ->
      begin match Datatypes.desc env.data ty with
      | Ttuple types when List.length patterns = List.length types ->
          List.foldi patterns ~init:(Ok env) ~f:(fun i env pattern ->
              let* env = env in
              let _, ty = List.nth_exn types i in
              proof_pattern env pattern ty
                (R.Expr.tuple_get ~loc:(loc pattern.pat_loc) value i))
      | _ -> error pattern.pat_loc "The proof pattern does not match its input type"
      end
  | Pconstr _ | Pconst _ ->
      error pattern.pat_loc "A proof parameter needs an irrefutable pattern"

let bind_proof_pattern env pattern ty value =
  match List.find_a_dup (pat_names pattern) ~compare:String.compare with
  | Some x -> error pattern.S.pat_loc (Printf.sprintf "Duplicate proof variable %s" x)
  | None -> proof_pattern env pattern ty value

let packed_type = function
  | [] -> Predef.type_unit
  | [ ty ] -> ty
  | types -> Btype.newgenty (Ttuple (List.map types ~f:(fun ty -> (None, ty))))

let packed_value ~loc:l = function
  | [] -> unit_value ~loc:l
  | [ value ] -> value
  | values -> R.Expr.tuple ~loc:l values

let unpacked_value ~loc:l types value =
  match types with
  | [] -> []
  | [ _ ] -> [ value ]
  | types -> List.mapi types ~f:(fun i _ -> R.Expr.tuple_get ~loc:l value i)

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
  | Tvar q when List.Assoc.mem env.ctx.given.preds (logical_key env q) ~equal:String.equal
    ->
      let key = logical_key env q in
      let display = qualid_key q in
      let* () =
        if List.mem env.ctx.given.proof_support.opaque_predicates key ~equal:String.equal
        then
          error head.term_loc
            "The definition of this predicate is hidden by its module signature"
        else Ok ()
      in
      begin match
        List.Assoc.find env.ctx.given.predicate_bodies key ~equal:String.equal
      with
      | None -> Ok None
      | Some body ->
          let bindings = predicate_existentials body.definition in
          let* types =
            all witnesses ~f:(fun (witness : S.id) ->
                match
                  List.filter bindings ~f:(fun (id, _) ->
                      String.equal id.S.pid_str witness.pid_str)
                with
                | [] ->
                    error witness.pid_loc
                      (Printf.sprintf "Predicate %s has no existential named %s" display
                         witness.pid_str)
                | [ (_, Some ty) ] ->
                    let* ty = Source.ocaml_type body.environment ~at:witness.pid_loc ty in
                    Ok (Some (body.project_type ty))
                | [ (_, None) ] ->
                    error witness.pid_loc "An existential variable needs a type"
                | _ ->
                    error witness.pid_loc
                      (Printf.sprintf "Existential name %s is ambiguous in predicate %s"
                         witness.pid_str display))
          in
          Ok (Some types)
      end
  | _ -> error t.term_loc "Expected a predicate applied to its arguments"

let rec proof_result_types env (body : S.proof_expr) =
  match body.proof_desc with
  | Proof_value t
    when is_ghost_fpu t || Option.equal String.equal (ghost_operation t) (Some "write") ->
      Ok (Some [])
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
            let branch_env =
              List.fold types
                ~init:{ env with var_types = types @ env.var_types }
                ~f:(fun env (x, _) -> bind env x (Raven x))
            in
            let* types = proof_result_types branch_env body in
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
  | Proof_value t when Option.equal String.equal (ghost_operation t) (Some "write") ->
      begin match snd (spine t []) with
      | [ location; value ] ->
          let* field, location = ghost_value_location env location in
          let* () =
            Source.check_logical_expression env.ctx.given.env
              ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types
              ~expected:field.field_value value
          in
          let* value = expected_formula env (Some field.field_value) value in
          unit_statement (R.Stmt.assign ~loc:l [ location ] (R.Stmt.expr_rhs value))
      | _ -> error t.term_loc "Ghost.write expects a location and a value"
      end
  | Proof_value t when Option.equal String.equal (ghost_operation t) (Some "read") ->
      begin match (snd (spine t []), targets) with
      | [ location ], [ target ] ->
          let* field, location = ghost_value_location env location in
          let* () =
            if
              Ctype.is_equal env.ctx.given.env false [ field.field_value ]
                [ target.target_type ]
            then Ok ()
            else error t.term_loc "The ghost read has a different result type"
          in
          Ok [ R.Stmt.assign ~loc:l [ target_expr target ] (R.Stmt.expr_rhs location) ]
      | _ -> error t.term_loc "Bind the result of Ghost.read location"
      end
  | Proof_value t when Option.equal String.equal (ghost_operation t) (Some "alloc") ->
      begin match (snd (spine t []), targets) with
      | [ initializers ], [ target ] ->
          let* owner = Source.ghost_type env.ctx.given.env ~at:t.term_loc in
          let* () =
            if Ctype.is_equal env.ctx.given.env false [ owner ] [ target.target_type ]
            then Ok ()
            else error t.term_loc "Ghost.alloc returns Ghost.t"
          in
          let* fields = ghost_initializers env ~owner initializers in
          Ok [ R.Stmt.assign ~loc:l [ target_expr target ] (R.Stmt.new_rhs fields) ]
      | _ -> error t.term_loc "Bind the result of Ghost.alloc initializers"
      end
  | Proof_value t ->
      begin match proof_signature env t with
      | Some signature ->
          let* () =
            if
              Ctype.is_equal env.ctx.given.env false
                [ packed_type signature.lemma_outputs ]
                [ packed_type (List.map targets ~f:(fun t -> t.target_type)) ]
            then Ok ()
            else
              error t.term_loc
                "The proof expression has a different result type from its binding"
          in
          let* call, outputs = proof_call env t in
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
                      let raven = Names.fresh env.ctx.procedure.names "result" in
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
                    let raven = Names.fresh env.ctx.procedure.names "result" in
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
                let* () =
                  Source.check_logical_expression env.ctx.given.env
                    ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types
                    ~expected:(packed_type (List.map targets ~f:(fun t -> t.target_type)))
                    value
                in
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
                let* () =
                  Source.check_logical_expression env.ctx.given.env
                    ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types
                    ~expected:target.target_type value
                in
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
      proof_binding env pattern rhs (fun env -> proof_expression env targets rest)
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

and proof_binding ?(ghost_rhs = false) env pattern rhs continuation =
  let l = loc rhs.S.proof_loc in
  let* inferred = proof_result_types env rhs in
  let* bindings = proof_binding_types env pattern inferred in
  let* declarations =
    all bindings ~f:(fun (id, ty) ->
        let id = Option.value id ~default:(S.mk_id ~loc:pattern.pat_loc "discard") in
        let raven = Names.fresh env.ctx.procedure.names id.pid_str in
        let* raven_type = typ env.ctx ~at:id.pid_loc ty in
        Ok
          ( id,
            { target_name = raven; target_type = ty },
            R.Stmt.local ~loc:(loc id.pid_loc) ~ghost:true ~typ:raven_type
              (ident ~loc:l raven) ))
  in
  let* rhs_statements =
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
  let* rest = continuation env in
  let rhs =
    if ghost_rhs then [ R.Stmt.ghost_block ~loc:(loc rhs.proof_loc) rhs_statements ]
    else rhs_statements
  in
  Ok (List.concat_map declarations ~f:(fun (_, _, stmts) -> stmts) @ rhs @ rest)

(** Ghost annotations share the checked lemma expression language. *)
let ghost ctx ~(after : Lexing.position) ~(before : Lexing.position) =
  let between (a : Annotation.t) =
    a.loc.loc_start.pos_cnum >= after.pos_cnum
    && a.loc.loc_end.pos_cnum <= before.pos_cnum
    && List.mem
         [ Annotation.Ghost; Annotation.Proof ]
         (Annotation.kind a) ~equal:Poly.equal
  in
  let* blocks =
    all (List.filter ctx.given.annotations ~f:between) ~f:(fun annotation ->
        match Annotation.kind annotation with
        | Annotation.Proof ->
            let* body = Annotation.proof annotation in
            let* statements = proof_expression (scope_env ctx) [] body in
            Ok [ R.Stmt.ghost_block ~loc:(loc annotation.loc) statements ]
        | _ ->
            let* statements = Annotation.ghost_stmts annotation in
            all statements ~f:(proof_statement (scope_env ctx)))
  in
  Ok (List.concat blocks)

(** Free names in proof expressions, respecting lexical bindings. *)
let rec proof_names (body : S.proof_expr) =
  match body.proof_desc with
  | Proof_value t | Proof_assert t | Proof_unfold (t, _) -> term_names t
  | Proof_fold (t, witnesses) ->
      term_names t @ List.concat_map witnesses ~f:(fun (_, t) -> term_names t)
  | Proof_seq (a, b) -> proof_names a @ proof_names b
  | Proof_let (pattern, rhs, rest) ->
      proof_names rhs
      @ List.filter (proof_names rest) ~f:(fun name ->
          not (List.mem (pat_names pattern) name ~equal:String.equal))
  | Proof_if (t, a, b) -> term_names t @ proof_names a @ proof_names b
  | Proof_match (t, cases) ->
      term_names t
      @ List.concat_map cases ~f:(fun (p, body) ->
          List.filter (proof_names body) ~f:(fun name ->
              not (List.mem (pat_names p) name ~equal:String.equal)))

let stateful_access access_proofs (e : Typedtree.expression) =
  let key = (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum) in
  match List.Assoc.find access_proofs key ~equal:Poly.equal with
  | None -> Ok false
  | Some annotation ->
      Result.map (Annotation.scope annotation) ~f:(fun scope ->
          Option.is_some scope.scope_state)

let atomic_read_argument (e : Typedtree.expression) =
  match e.exp_desc with
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, [ (_, Arg argument) ])
    when Option.equal String.equal (atomic_name path) (Some "get") ->
      Some argument
  | _ -> None

(** State stays local to a directly nested pair of explicitly stateful reads. *)
let nested_stateful_read access_proofs e =
  match atomic_read_argument e with
  | Some argument when Option.is_some (atomic_read_argument argument) ->
      let* outer = stateful_access access_proofs e in
      let* inner = stateful_access access_proofs argument in
      Ok (Option.some_if (outer && inner) argument)
  | _ -> Ok None

(** A checked wrapper invokes the original operation once. *)
let access_proof ctx annotation ~result_type ?(input_types = []) ?(output_types = []) run
    =
  let* scope = Annotation.scope annotation in
  let operation = scope.scope_operation and body = scope.scope_body in
  let uses_operation body =
    List.mem (proof_names body) operation.pid_str ~equal:String.equal
  in
  let reject_operation visible body =
    if visible && uses_operation body then
      error body.S.proof_loc "Bind the attached operation once in an unconditional let"
    else Ok ()
  in
  let ghost_statements env body =
    let* statements = proof_expression env [] body in
    Ok [ R.Stmt.ghost_block ~loc:(loc body.S.proof_loc) statements ]
  in
  let finish_state env (state : S.term) =
    let* ty = proof_value_type env state in
    match ty with
    | None -> error state.term_loc "Add a type annotation to the output proof state"
    | Some ty ->
        let* () =
          Source.check_logical_expression env.ctx.given.env
            ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types ~expected:ty
            state
        in
        let* value = expected_formula env (Some ty) state in
        let raven = Names.fresh ctx.procedure.names "proof_state" in
        let* raven_type = typ ctx ~at:state.term_loc ty in
        let l = loc state.term_loc in
        let result = R.Expr.var ~loc:l (name ~loc:l raven) in
        ctx.procedure.proof_state <- Some (result, ty);
        Ok
          (R.Stmt.local ~loc:l ~ghost:true ~typ:raven_type (ident ~loc:l raven)
          @ [
              R.Stmt.ghost_block ~loc:l
                [ R.Stmt.assign ~loc:l [ result ] (R.Stmt.expr_rhs value) ];
            ])
  in
  let rec after env ~operation_visible ~result_name ~result_visible body =
    let* () = reject_operation operation_visible body in
    let unchanged (t : S.term) =
      match t.term_desc with
      | Tvar (Qid id) -> result_visible && String.equal id.pid_str result_name
      | _ -> false
    in
    match body.S.proof_desc with
    | Proof_value t when Option.is_none scope.scope_state && unchanged t -> Ok []
    | Proof_value { term_desc = Ttuple [ runtime; state ]; _ }
      when Option.is_some scope.scope_state && unchanged runtime ->
        finish_state env state
    | Proof_seq (first, rest) ->
        let* first = ghost_statements env first in
        let* rest = after env ~operation_visible ~result_name ~result_visible rest in
        Ok (first @ rest)
    | Proof_let (pattern, rhs, rest) ->
        proof_binding ~ghost_rhs:true env pattern rhs (fun env ->
            after env
              ~operation_visible:
                (operation_visible
                && not
                     (List.mem (pat_names pattern) operation.pid_str ~equal:String.equal)
                )
              ~result_name
              ~result_visible:
                (result_visible
                && not (List.mem (pat_names pattern) result_name ~equal:String.equal))
              rest)
    | _ ->
        error body.proof_loc
          (if Option.is_some scope.scope_state then
             "A stateful scope must return (unchanged operation result, output state)"
           else
             "An access proof must return the unchanged result of the attached operation")
  in
  let operation_argument visible body =
    match body.S.proof_desc with
    | Proof_value t when visible ->
        begin match spine t [] with
        | { term_desc = Tvar (Qid id); _ }, [ argument ]
          when String.equal id.pid_str operation.pid_str ->
            Some argument
        | _ -> None
        end
    | _ -> None
  in
  let rec runtime_binding (p : S.pat) =
    match p.pat_desc with
    | Pid id -> Some id
    | Pcast (p, _) -> runtime_binding p
    | _ -> None
  in
  let rec operation_result (p : S.pat) =
    if List.is_empty output_types then runtime_binding p
    else
      match p.pat_desc with
      | Ptuple [ runtime; _ ] -> runtime_binding runtime
      | Pcast (p, _) -> operation_result p
      | _ -> None
  in
  let rec before env visible body =
    match body.S.proof_desc with
    | Proof_let (pattern, rhs, rest) when Option.is_some (operation_argument visible rhs)
      ->
        let argument = Option.value_exn (operation_argument visible rhs) in
        let* () =
          Source.check_logical_expression env.ctx.given.env
            ~functions:(List.map env.funcs ~f:fst) ~variables:env.var_types
            ~expected:(packed_type input_types) argument
        in
        let* argument = expected_formula env (Some (packed_type input_types)) argument in
        let arguments = unpacked_value ~loc:(loc rhs.proof_loc) input_types argument in
        let* statements, result, outputs = run arguments in
        let result_value, result_ty =
          if List.is_empty output_types then (result, result_type)
          else
            ( R.Expr.tuple ~loc:(loc rhs.proof_loc)
                [ result; packed_value ~loc:(loc rhs.proof_loc) outputs ],
              packed_type [ result_type; packed_type output_types ] )
        in
        let* env = bind_proof_pattern env pattern result_ty result_value in
        begin match operation_result pattern with
        | None ->
            error pattern.pat_loc
              "Bind the operation's runtime result to a variable of its original type"
        | Some id ->
            let* rest =
              after env
                ~operation_visible:
                  (not
                     (List.mem (pat_names pattern) operation.pid_str ~equal:String.equal))
                ~result_name:id.pid_str ~result_visible:true rest
            in
            Ok (statements @ rest)
        end
    | Proof_let (pattern, rhs, rest) ->
        let* () = reject_operation visible rhs in
        proof_binding ~ghost_rhs:true env pattern rhs (fun env ->
            before env
              (visible
              && not (List.mem (pat_names pattern) operation.pid_str ~equal:String.equal)
              )
              rest)
    | Proof_seq (first, rest) ->
        let* () = reject_operation visible first in
        let* first = ghost_statements env first in
        let* rest = before env visible rest in
        Ok (first @ rest)
    | _ ->
        error body.proof_loc
          "An access proof needs one unconditional let binding of the attached operation"
  in
  let* env =
    match scope.scope_state with
    | None -> Ok (scope_env ctx)
    | Some pattern ->
        let value, ty = proof_state ctx ~at:pattern.pat_loc in
        bind_proof_pattern (scope_env ctx) pattern ty value
  in
  let visible =
    not
      (Option.exists scope.scope_state ~f:(fun p ->
           List.mem (pat_names p) operation.pid_str ~equal:String.equal))
  in
  before env visible body

let return_proof ctx annotation ~result_type ~result =
  let* adapter = Annotation.returns annotation in
  if List.is_empty ctx.procedure.ghost_returns then
    error annotation.Annotation.loc "Ghost.returns requires declared ghost results"
  else
    let* env =
      bind_proof_pattern (scope_env ctx) adapter.returns_result result_type result
    in
    let value, ty = proof_state ctx ~at:adapter.returns_state.pat_loc in
    let* env = bind_proof_pattern env adapter.returns_state ty value in
    let targets =
      List.map ctx.procedure.ghost_returns ~f:(fun (_, raven, ty) ->
          { target_name = raven; target_type = ty })
    in
    let* statements = proof_expression env targets adapter.returns_body in
    Ok [ R.Stmt.ghost_block ~loc:(loc annotation.loc) statements ]
