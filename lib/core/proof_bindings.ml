(** Static proof declarations owned by source modules. *)

open Base
module S = Caravan_spec.Spec_ast

let ( let* ) = Result.( >>= )

type kind = Predicate of S.predicate * S.term | Lemma of S.proof_decl

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
  let relevant =
    relevant_constraints inventory.Module_inventory.constraints source.Source.proof_scopes
      scope
  in
  match kind with
  | Lemma _ -> List.is_empty relevant
  | Predicate _ ->
      List.for_all relevant ~f:(fun (ancestor, constraint_) ->
          visible_in_constraint scope name ancestor constraint_)

let opaque t binding =
  match binding.kind with
  | Lemma _ -> false
  | Predicate _ ->
      binding.exported
      && not
           (List.is_empty
              (relevant_constraints t.constraints t.scopes binding.entry.scope))

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
        | None -> substitution
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

let supported entry =
  match entry.Proof_scopes.declaration with
  | S.Proof_predicate predicate ->
      begin match predicate.pred_body with
      | Some body -> Ok (Predicate (predicate, body), predicate.pred_params)
      | None ->
          Report.unsupported entry.name.pid_loc
            "A declaration-only predicate in a module proof"
      end
  | Proof_invariant { inv_name; inv_params; inv_state; inv_body } ->
      let predicate =
        {
          S.pred_name = inv_name;
          pred_params = inv_params @ [ inv_state ];
          pred_body = Some inv_body;
          pred_persistent = true;
        }
      in
      Ok (Predicate (predicate, inv_body), predicate.pred_params)
  | Proof_lemma { lemma_params; lemma_returns; _ } ->
      Ok (Lemma entry.declaration, lemma_params @ lemma_returns)
  | Proof_module _ | Proof_type _ | Proof_resource _ | Proof_au _ | Proof_field _
  | Proof_function _ | Proof_state _ | Proof_view _ | Proof_action _ ->
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

let functor_ancestor scopes scope =
  List.find scopes.Proof_scopes.scopes ~f:(fun ancestor ->
      Option.is_some (drop_prefix ancestor.namespace scope.Proof_scopes.namespace)
      && not (List.is_empty ancestor.parameters))

let build ~fresh (source : Source.t) (inventory : Module_inventory.t) =
  let scopes = source.proof_scopes in
  let projection = public_projection inventory scopes in
  let entries =
    List.filter scopes.declarations ~f:(fun entry ->
        Option.is_some entry.Proof_scopes.scope.owner)
  in
  let* () =
    List.fold_result entries ~init:[] ~f:(fun previous entry ->
        match
          List.find previous ~f:(fun earlier ->
              same_owner earlier.Proof_scopes.scope.owner entry.scope.owner
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
              Report.unsupported entry.name.pid_loc
                (Printf.sprintf "A proof declaration inside functor %s"
                   (String.concat ~sep:"." ancestor.namespace))
        in
        let* kind, parameters = supported entry in
        let* () =
          match
            List.find inventory.values ~f:(fun value ->
                List.equal String.equal value.Module_inventory.namespace scope.namespace
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
        let* private_types = parameter_types environment parameters in
        let* public_types =
          let declared =
            match kind with
            | Lemma _ -> None
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
      if String.equal key binding.backend || String.equal key binding.public_key then
        Some binding.backend
      else None)

let resolve t ~scope ~environment (q : S.qualid) =
  match q with
  | Qid id ->
      let candidate =
        List.find (private_bindings t ~scope) ~f:(fun binding ->
            String.equal binding.entry.name.pid_str id.pid_str)
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
          List.find_map t.bindings ~f:(fun binding ->
              if
                binding.exported
                && same_owner binding.entry.scope.owner (Some owner)
                && String.equal binding.entry.name.pid_str id.pid_str
              then Some binding.public_key
              else None))
