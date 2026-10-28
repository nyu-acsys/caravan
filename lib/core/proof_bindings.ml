(** Static proof declarations owned by source modules. *)

open Base
module S = Caravan_spec.Spec_ast

let ( let* ) = Result.( >>= )

type predicate_definition =
  | Plain of S.term
  | Stateful of {
      state : string;
      fields : S.state_field list;
      body : S.term;
      environment : Env.t;
      state_scope : Proof_scopes.scope;
    }
  | View of S.term

type kind =
  | Predicate of S.predicate * predicate_definition
  | Lemma of S.proof_decl
  | Function of S.proof_decl
  | State of S.state_field list
  | Action of S.proof_decl
  | Resource of Source.proof_resource
  | Field of Source.proof_field
  | Atomic of Source.proof_au

type binding = {
  entry : Proof_scopes.entry;
  kind : kind;
  backend : string;
  public_key : string;
  environment : Env.t;
  private_types : Types.type_expr list;
  public_types : Types.type_expr list;
  exported : bool;
}

type t = {
  scopes : Proof_scopes.t;
  bindings : binding list;
  values : Module_inventory.value list;
  constraints : Module_inventory.resource_constraint list;
  projection : Subst.t;
}

let public_type t typ = Subst.type_expr t.projection typ
let same_owner a b = Option.equal Path.same a b

let drop_prefix prefix names =
  let rec go prefix names =
    match (prefix, names) with
    | [], names -> Some names
    | p :: ps, n :: ns when String.equal p n -> go ps ns
    | _ -> None
  in
  go prefix names

let functor_ancestor scopes scope =
  List.find scopes.Proof_scopes.scopes ~f:(fun ancestor ->
      Option.is_some (drop_prefix ancestor.namespace scope.Proof_scopes.namespace)
      && not (List.is_empty ancestor.parameters))

let contains (outer : Location.t) (inner : Location.t) =
  outer.loc_start.pos_cnum <= inner.loc_start.pos_cnum
  && inner.loc_end.pos_cnum <= outer.loc_end.pos_cnum

let scope_for_namespace t namespace =
  List.filter t.scopes.scopes ~f:(fun scope ->
      Option.is_some (drop_prefix scope.Proof_scopes.namespace namespace))
  |> List.max_elt ~compare:(fun a b ->
      Int.compare (List.length a.Proof_scopes.namespace) (List.length b.namespace))

let scope_for_location t location =
  List.filter t.scopes.scopes ~f:(fun scope ->
      contains scope.Proof_scopes.source_location location)
  |> List.max_elt ~compare:(fun a b ->
      Int.compare (List.length a.Proof_scopes.namespace) (List.length b.namespace))

let constraints_for t binding =
  List.filter t.constraints ~f:(fun constraint_ ->
      same_owner constraint_.Module_inventory.owner binding.entry.scope.owner)

let own_constraints constraints scope =
  List.filter constraints ~f:(fun constraint_ ->
      same_owner constraint_.Module_inventory.owner scope.Proof_scopes.owner)

let restricting_constraints constraints scope =
  List.filter (own_constraints constraints scope) ~f:(fun constraint_ ->
      constraint_.Module_inventory.restricts_visibility)

let rec signature_member signature = function
  | [] -> Some signature
  | name :: rest ->
      Option.bind
        (List.Assoc.find signature.Module_inventory.signature_modules name
           ~equal:String.equal) ~f:(fun member ->
          signature_member member.signature_body rest)

let visible_in_constraint scope name ancestor constraint_ =
  match drop_prefix ancestor.Proof_scopes.namespace scope.Proof_scopes.namespace with
  | None -> true
  | Some suffix ->
      begin match signature_member constraint_.Module_inventory.signature suffix with
      | None -> false
      | Some signature ->
          List.Assoc.mem signature.signature_resources name ~equal:String.equal
      end

let relevant_constraints constraints scopes scope =
  let ancestors =
    List.filter scopes.Proof_scopes.scopes ~f:(fun ancestor ->
        Option.is_some
          (drop_prefix ancestor.Proof_scopes.namespace scope.Proof_scopes.namespace))
  in
  List.concat_map ancestors ~f:(fun ancestor ->
      List.map (restricting_constraints constraints ancestor) ~f:(fun constraint_ ->
          (ancestor, constraint_)))

let exported inventory source scope name kind =
  let template = functor_ancestor source.Source.proof_scopes scope in
  let relevant =
    relevant_constraints inventory.Module_inventory.constraints source.Source.proof_scopes
      scope
  in
  if Option.is_some template then false
  else
    match kind with
    | Lemma _ | Function _ | State _ | Action _ | Resource _ | Field _ | Atomic _ ->
        List.is_empty relevant
    | Predicate _ ->
        List.for_all relevant ~f:(fun (ancestor, constraint_) ->
            visible_in_constraint scope name ancestor constraint_)

let remaining_constraints t ~scope binding =
  relevant_constraints t.constraints t.scopes binding.entry.scope
  |> List.filter ~f:(fun (ancestor, constraint_) ->
      let boundary =
        Option.value
          (Proof_scopes.find_owner t.scopes constraint_.Module_inventory.boundary)
          ~default:ancestor
      in
      not
        (Option.exists scope ~f:(fun caller ->
             Option.is_some
               (drop_prefix boundary.Proof_scopes.namespace caller.Proof_scopes.namespace))))

let visible t ~scope binding =
  let inside_template =
    match functor_ancestor t.scopes binding.entry.scope with
    | None -> true
    | Some owner ->
        Option.exists scope ~f:(fun scope ->
            Option.is_some (drop_prefix owner.namespace scope.Proof_scopes.namespace))
  in
  let relevant = remaining_constraints t ~scope binding in
  inside_template
  &&
  match binding.kind with
  | Lemma _ | Function _ | State _ | Action _ | Resource _ | Field _ | Atomic _ ->
      List.is_empty relevant
  | Predicate _ ->
      List.for_all relevant ~f:(fun (ancestor, constraint_) ->
          visible_in_constraint binding.entry.scope binding.entry.name.pid_str ancestor
            constraint_)

let opaque_at t ~scope binding =
  match binding.kind with
  | Lemma _ | Function _ | State _ | Action _ | Resource _ | Field _ | Atomic _ -> false
  | Predicate _ -> not (List.is_empty (remaining_constraints t ~scope binding))

let opaque t binding = binding.exported && opaque_at t ~scope:None binding

let local_exports t ~scope =
  List.filter t.bindings ~f:(fun binding ->
      (not binding.exported) && visible t ~scope binding)

let opaque_keys t =
  List.filter_map t.bindings ~f:(fun binding ->
      Option.some_if (opaque t binding) binding.public_key)

let rec signature_type_projection substitution owner signature =
  let substitution =
    List.fold signature.Module_inventory.signature_types ~init:substitution
      ~f:(fun substitution (name, declaration) ->
        Subst.add_type declaration.Typedtree.typ_id (Path.Pdot (owner, name)) substitution)
  in
  List.fold signature.signature_modules ~init:substitution
    ~f:(fun substitution (name, nested) ->
      let child = Path.Pdot (owner, name) in
      let substitution =
        Option.value_map nested.signature_id ~default:substitution ~f:(fun id ->
            Subst.add_module id child substitution)
      in
      signature_type_projection substitution child nested.signature_body)

let public_projection inventory scopes =
  let module_substitution =
    List.fold inventory.Module_inventory.aliases ~init:Subst.identity
      ~f:(fun substitution (alias, target) ->
        match alias with
        | Path.Pident id -> Subst.add_module id target substitution
        | Pdot _ | Papply _ | Pextra_ty _ -> substitution)
  in
  let substitution =
    List.fold inventory.Module_inventory.types ~init:module_substitution
      ~f:(fun substitution definition ->
        match Proof_scopes.find_namespace scopes definition.namespace with
        | None ->
            begin match
              List.find definition.paths ~f:(function Path.Pdot _ -> true | _ -> false)
            with
            | None -> substitution
            | Some path -> Subst.add_type definition.declaration.typ_id path substitution
            end
        | Some scope ->
            begin match scope.owner with
            | None -> substitution
            | Some owner ->
                let name = definition.declaration.Typedtree.typ_name.txt in
                Subst.add_type definition.declaration.typ_id
                  (Path.Pdot (owner, name))
                  substitution
            end)
  in
  substitution

let parameter_types environment parameters =
  List.map parameters ~f:(fun (id, pty) ->
      Source.ocaml_type environment ~at:id.S.pid_loc pty)
  |> Result.all

let state_entry scopes entries ~scope ~environment (name : S.qualid) =
  let candidate =
    match name with
    | Qid id ->
        List.filter_map entries ~f:(fun entry ->
            match entry.Proof_scopes.declaration with
            | S.Proof_state _
              when String.equal entry.name.pid_str id.pid_str
                   && Option.is_some
                        (drop_prefix entry.scope.namespace scope.Proof_scopes.namespace)
              ->
                Some entry
            | _ -> None)
        |> List.max_elt ~compare:(fun a b ->
            Int.compare
              (List.length a.Proof_scopes.scope.namespace)
              (List.length b.scope.namespace))
    | Qdot (parent, id) ->
        Option.bind (Source.module_path environment parent) ~f:(fun owner ->
            let owner = Proof_scopes.canonical_owner scopes owner in
            List.find entries ~f:(fun entry ->
                match entry.Proof_scopes.declaration with
                | S.Proof_state _ ->
                    same_owner entry.scope.owner (Some owner)
                    && String.equal entry.name.pid_str id.pid_str
                | _ -> false))
  in
  candidate

let state_visible constraints scopes ~scope entry =
  relevant_constraints constraints scopes entry.Proof_scopes.scope
  |> List.for_all ~f:(fun (ancestor, constraint_) ->
      let boundary =
        Option.value
          (Proof_scopes.find_owner scopes constraint_.Module_inventory.boundary)
          ~default:ancestor
      in
      Option.is_some (drop_prefix boundary.namespace scope.Proof_scopes.namespace))

let view_declaration inventory scope name =
  List.find_map
    (List.rev (own_constraints inventory.Module_inventory.constraints scope))
    ~f:(fun constraint_ ->
      Option.map
        (List.Assoc.find constraint_.Module_inventory.signature.signature_resources name
           ~equal:String.equal) ~f:(fun formal -> (constraint_, formal)))

let supported (source : Source.t) (inventory : Module_inventory.t) entry =
  let scope = entry.Proof_scopes.scope in
  let environment = Source.annotation_env source scope.environment in
  match entry.Proof_scopes.declaration with
  | S.Proof_predicate predicate ->
      begin match predicate.pred_body with
      | Some body -> Ok (Predicate (predicate, Plain body), predicate.pred_params)
      | None ->
          Report.unsupported entry.name.pid_loc
            "A declaration-only predicate in a module proof"
      end
  | Proof_invariant { inv_name; inv_params; inv_state = state, state_type; inv_body } ->
      let* state_definition =
        match state_type with
        | PTtyapp (name, []) ->
            begin match
              state_entry source.proof_scopes source.proof_scopes.declarations ~scope
                ~environment name
            with
            | None -> Ok None
            | Some definition ->
                if
                  state_visible inventory.constraints source.proof_scopes ~scope
                    definition
                then
                  begin match definition.declaration with
                  | Proof_state { state_fields; _ } ->
                      let environment =
                        Source.annotation_env source definition.scope.environment
                      in
                      Ok (Some (state_fields, environment, definition.scope))
                  | _ -> Ok None
                  end
                else
                  Error
                    (Report.error Type (S.qualid_loc name)
                       "The state is private to its module")
            end
        | _ -> Ok None
      in
      let params, definition =
        match state_definition with
        | Some (fields, environment, state_scope) ->
            ( inv_params,
              Stateful
                {
                  state = state.pid_str;
                  fields;
                  body = inv_body;
                  environment;
                  state_scope;
                } )
        | None -> (inv_params @ [ (state, state_type) ], Plain inv_body)
      in
      let predicate =
        {
          S.pred_name = inv_name;
          pred_params = params;
          pred_body = None;
          pred_persistent = true;
        }
      in
      Ok (Predicate (predicate, definition), predicate.pred_params)
  | Proof_view { view_name; view_params; view_value } ->
      begin match view_declaration inventory scope view_name.pid_str with
      | None ->
          Error
            (Report.error Type view_name.pid_loc
               (Printf.sprintf
                  "The view %s has no resource declaration giving its value type"
                  view_name.pid_str))
      | Some (_, formal) ->
          let declared = formal.Module_inventory.declaration in
          if List.length declared.pred_params <> List.length view_params + 1 then
            Error
              (Report.error Type view_name.pid_loc
                 ~related:[ (declared.pred_name.pid_loc, "Its declaration") ]
                 "A view has the parameters of its declaration but the last, its value")
          else
            let value = List.last_exn declared.pred_params in
            let predicate =
              {
                S.pred_name = view_name;
                pred_params = view_params @ [ value ];
                pred_body = None;
                pred_persistent = false;
              }
            in
            Ok (Predicate (predicate, View view_value), predicate.pred_params)
      end
  | Proof_state { state_fields; _ } -> Ok (State state_fields, [])
  | Proof_action _ -> Ok (Action entry.declaration, [])
  | Proof_lemma { lemma_params; lemma_returns; _ } ->
      Ok (Lemma entry.declaration, lemma_params @ lemma_returns)
  | Proof_function { function_params; function_result; function_name; _ } ->
      Ok
        ( Function entry.declaration,
          function_params @ [ (function_name, function_result) ] )
  | Proof_resource _ ->
      begin match
        List.find source.proof_resources ~f:(fun resource ->
            Poly.equal resource.resource_at entry.name.pid_loc)
      with
      | Some resource -> Ok (Resource resource, [])
      | None ->
          Error
            (Report.error Type entry.name.pid_loc
               "Missing elaborated resource declaration")
      end
  | Proof_field _ ->
      begin match
        List.find source.proof_fields ~f:(fun field ->
            Poly.equal field.field_at entry.name.pid_loc)
      with
      | Some field -> Ok (Field field, [])
      | None ->
          Error
            (Report.error Type entry.name.pid_loc
               "Missing elaborated ghost field declaration")
      end
  | Proof_au _ ->
      begin match
        List.find source.proof_aus ~f:(fun au -> Poly.equal au.au_at entry.name.pid_loc)
      with
      | Some au -> Ok (Atomic au, [])
      | None ->
          Error (Report.error Type entry.name.pid_loc "Missing elaborated AU facade")
      end
  | Proof_module _ | Proof_type _ ->
      Report.unsupported entry.name.pid_loc
        (Printf.sprintf "A %s declaration in a module proof"
           (match entry.declaration with
           | Proof_type _ -> "type"
           | Proof_resource _ -> "resource"
           | Proof_au _ -> "atomic update"
           | Proof_field _ -> "field"
           | Proof_function _ -> "function"
           | Proof_state _ -> "state"
           | Proof_view _ -> "view"
           | Proof_action _ -> "action"
           | Proof_module _ -> "module"
           | Proof_predicate _ | Proof_invariant _ | Proof_lemma _ -> "proof"))

let declaration_namespace = function
  | S.Proof_state _ -> `State
  | Proof_action _ -> `Action
  | _ -> `Term

let term_binding binding =
  match binding.kind with State _ | Action _ -> false | _ -> true

let build ~fresh (source : Source.t) (inventory : Module_inventory.t) =
  let scopes = source.proof_scopes in
  let projection = public_projection inventory scopes in
  let projection =
    List.fold source.proof_types ~init:projection ~f:(fun projection data ->
        match
          ( data.Datatypes.id,
            List.find data.paths ~f:(function Path.Pdot _ -> true | _ -> false) )
        with
        | Some id, Some path -> Subst.add_type id path projection
        | _ -> projection)
  in
  let projection =
    List.fold source.proof_resources ~init:projection ~f:(fun projection resource ->
        Subst.add_module resource.Source.resource_id resource.resource_path projection)
  in
  let projection =
    List.fold source.proof_aus ~init:projection ~f:(fun projection au ->
        Subst.add_module au.Source.au_id au.au_path projection)
  in
  let entries =
    List.filter scopes.declarations ~f:(fun entry ->
        Option.is_some entry.Proof_scopes.scope.owner
        && match entry.declaration with S.Proof_type _ -> false | _ -> true)
  in
  let* () =
    List.fold_result entries ~init:[] ~f:(fun previous entry ->
        match
          List.find previous ~f:(fun earlier ->
              same_owner earlier.Proof_scopes.scope.owner entry.scope.owner
              && Poly.equal
                   (declaration_namespace earlier.declaration)
                   (declaration_namespace entry.declaration)
              && String.equal earlier.name.pid_str entry.name.pid_str)
        with
        | None -> Ok (entry :: previous)
        | Some earlier ->
            Error
              (Report.error Type entry.name.pid_loc
                 ~related:[ (earlier.name.pid_loc, "Its other declaration") ]
                 (Printf.sprintf "The proof name %s is repeated in this module"
                    entry.name.pid_str)))
    |> Result.map ~f:(fun _ -> ())
  in
  let* bindings =
    List.map entries ~f:(fun entry ->
        let scope = entry.Proof_scopes.scope in
        let* () =
          match functor_ancestor scopes scope with
          | None -> Ok ()
          | Some ancestor ->
              begin match (ancestor.parameters, entry.declaration) with
              | [ Named (Some _, _, _) ], (S.Proof_predicate _ | Proof_lemma _)
                when same_owner ancestor.owner scope.owner ->
                  Ok ()
              | _ ->
                  Report.unsupported entry.name.pid_loc
                    "This declaration or nested scope in a functor proof"
              end
        in
        let* kind, parameters = supported source inventory entry in
        let* () =
          match
            List.find inventory.values ~f:(fun value ->
                (match kind with State _ | Action _ -> false | _ -> true)
                && List.equal String.equal value.Module_inventory.namespace
                     scope.namespace
                &&
                match value.binding.Typedtree.vb_pat.pat_desc with
                | Tpat_var (id, _, _) -> String.equal (Ident.name id) entry.name.pid_str
                | _ -> false)
          with
          | None -> Ok ()
          | Some value ->
              Error
                (Report.error Type entry.name.pid_loc
                   ~related:[ (value.binding.vb_pat.pat_loc, "The runtime value") ]
                   (Printf.sprintf
                      "The proof name %s conflicts with a runtime value in this module"
                      entry.name.pid_str))
        in
        let environment = Source.annotation_env source scope.environment in
        let* private_types =
          match (kind, entry.declaration) with
          | Predicate (_, View _), Proof_view { view_name; view_params; _ } ->
              begin match view_declaration inventory scope view_name.pid_str with
              | None ->
                  Error
                    (Report.error Type view_name.pid_loc
                       "Missing resource declaration for view")
              | Some (constraint_, formal) ->
                  let* inputs = parameter_types environment view_params in
                  let value = List.last_exn formal.declaration.pred_params in
                  let signature_environment =
                    Source.annotation_env source formal.site.environment
                  in
                  let* output = parameter_types signature_environment [ value ] in
                  Ok
                    (inputs
                    @ List.map output ~f:(Subst.type_expr constraint_.substitution))
              end
          | _ -> parameter_types environment parameters
        in
        let* public_types =
          let declared =
            match kind with
            | Lemma _ | Function _ | State _ | Action _ | Resource _ | Field _ | Atomic _
              ->
                None
            | Predicate _ ->
                Option.bind
                  (List.last (restricting_constraints inventory.constraints scope))
                  ~f:(fun constraint_ ->
                    Option.map
                      (List.Assoc.find
                         constraint_.Module_inventory.signature.signature_resources
                         entry.name.pid_str ~equal:String.equal) ~f:(fun formal ->
                        (constraint_, formal)))
          in
          match declared with
          | None -> Ok (List.map private_types ~f:(Subst.type_expr projection))
          | Some (constraint_, formal) ->
              let signature_environment =
                Source.annotation_env source formal.site.environment
              in
              let* types =
                parameter_types signature_environment formal.declaration.pred_params
              in
              let projection =
                Option.value_map scope.owner ~default:projection ~f:(fun owner ->
                    signature_type_projection projection owner constraint_.signature)
              in
              Ok (List.map types ~f:(Subst.type_expr projection))
        in
        let base =
          String.uncapitalize
            (String.concat ~sep:"_" (scope.namespace @ [ entry.name.pid_str ]))
        in
        let backend = fresh base in
        let public_key = fresh (base ^ "_public") in
        Ok
          {
            entry;
            kind;
            backend;
            public_key;
            environment;
            private_types;
            public_types;
            exported = exported inventory source scope entry.name.pid_str kind;
          })
    |> Result.all
  in
  Ok
    {
      scopes;
      bindings;
      values = inventory.values;
      constraints = inventory.constraints;
      projection;
    }

let private_bindings t ~(scope : Proof_scopes.scope option) =
  match scope with
  | None -> []
  | Some scope ->
      List.filter t.bindings ~f:(fun binding ->
          Option.is_some (drop_prefix binding.entry.scope.namespace scope.namespace))
      |> List.sort ~compare:(fun a b ->
          Int.compare
            (List.length b.entry.scope.namespace)
            (List.length a.entry.scope.namespace))

let canonical_key t key =
  List.find_map t.bindings ~f:(fun binding ->
      if
        term_binding binding
        && (String.equal key binding.backend || String.equal key binding.public_key)
      then Some binding.backend
      else None)

let canonical_owner t path = Proof_scopes.canonical_owner t.scopes path

(** Expresses public signatures through the module paths visible in a lexical scope. *)
let context_type t ~environment =
  let replacements =
    List.filter_map t.scopes.scopes ~f:(fun scope ->
        match (scope.Proof_scopes.owner, List.last scope.namespace) with
        | Some owner, Some member ->
            let q = S.Qid (S.mk_id ~loc:scope.source_location member) in
            Option.bind (Source.module_path environment q) ~f:(fun path ->
                Option.some_if
                  (Path.same (canonical_owner t path) owner && not (Path.same owner path))
                  (owner, path))
        | _ -> None)
  in
  let rec path original =
    match List.Assoc.find replacements original ~equal:Path.same with
    | Some replacement -> replacement
    | None -> (
        match original with
        | Path.Pdot (parent, member) -> Path.Pdot (path parent, member)
        | Papply (head, argument) -> Path.Papply (path head, path argument)
        | Pextra_ty (parent, extra) -> Path.Pextra_ty (path parent, extra)
        | Pident _ -> original)
  in
  let rec typ original =
    match Types.get_desc original with
    | Tconstr (owner, arguments, _) ->
        Ctype.newconstr (path owner) (List.map arguments ~f:typ)
    | Ttuple fields ->
        Btype.newgenty
          (Ttuple (List.map fields ~f:(fun (label, field) -> (label, typ field))))
    | Tarrow (label, argument, result, mode) ->
        Btype.newgenty (Tarrow (label, typ argument, typ result, mode))
    | Tpoly (body, variables) -> Btype.newgenty (Tpoly (typ body, variables))
    | _ -> original
  in
  if List.is_empty replacements then Fn.id else typ

let action_key t ~scope (id : S.id) =
  List.find_map (private_bindings t ~scope) ~f:(fun binding ->
      match binding.kind with
      | Action _ when String.equal binding.entry.name.pid_str id.pid_str ->
          Some binding.backend
      | _ -> None)

let resolve t ~scope ~environment (q : S.qualid) =
  match q with
  | Qid id ->
      let candidate =
        List.find (private_bindings t ~scope) ~f:(fun binding ->
            term_binding binding && String.equal binding.entry.name.pid_str id.pid_str)
      in
      Option.bind candidate ~f:(fun binding ->
          let runtime =
            Option.bind (Source.value_path environment q) ~f:(fun path ->
                List.find_map t.values ~f:(fun value ->
                    if
                      List.exists value.paths ~f:(Path.same path)
                      && (Option.is_some
                            (drop_prefix binding.entry.scope.namespace value.namespace)
                         || contains binding.entry.scope.source_location
                              value.binding.vb_pat.pat_loc)
                    then
                      match value.binding.vb_pat.pat_desc with
                      | Tpat_var (id, _, _) -> Some id
                      | _ -> None
                    else None))
          in
          Some
            (Option.value_map runtime ~default:binding.backend ~f:(fun id ->
                 "$runtime$" ^ Ident.unique_name id)))
  | Qdot (parent, id) ->
      Option.bind (Source.module_path environment parent) ~f:(fun owner ->
          let owner = canonical_owner t owner in
          List.find_map t.bindings ~f:(fun binding ->
              if
                term_binding binding && visible t ~scope binding
                && same_owner binding.entry.scope.owner (Some owner)
                && String.equal binding.entry.name.pid_str id.pid_str
              then Some binding.public_key
              else None))
