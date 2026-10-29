(** The translation of OCaml implementations to Raven programs.

    So far: top-level functions on integers, booleans, unit, tuples and variant types,
    with their contracts. A function becomes a procedure, and a variant type a data type
    (see {!Datatypes}). Expressions are put in A-normal form, since a call is a statement
    in Raven; arguments are evaluated right to left, as OCaml does. *)

open Base
open Translate_context
open Procedures
open Program_items
open Proof_declarations

let program (source : Source.t) : (R.Program.t * origin list, error) Result.t =
  let* scopes = Program_scopes.run source in
  let {
    Program_scopes.annotations;
    linearizations;
    initializations;
    fresh;
    source;
    implementation;
    proof_implementation;
    definition_resource;
    definition_target;
    inventory;
    scoped_binding;
    declaration_scope;
    declaration_environment;
    definition_member_name;
    libraries;
    funcs;
    access_proofs;
    return_proofs;
    alias_path;
    types;
    public_types;
    generics;
    generic_proofs;
    module_contexts;
    declaration_context;
    asset_context;
    context_for_group;
    generic_proof_types;
    proof_worker;
    scoped_proofs;
  } =
    scopes
  in
  let* decls = Program_declarations.run scopes in
  let {
    Program_declarations.source;
    all_resources;
    all_resource_views;
    resource_view;
    private_ra_types;
    proof_assets;
    layouts;
    checked_modules;
    checked_operations;
    pure;
    is_pure;
    pure_name;
    pure_reference;
    proc_name;
    body_proc_name;
    body_pure_name;
    body_pure_reference;
    body_owner;
    body_module_context;
    body_destination;
    runtime_destinations;
    with_body_names;
    procedure_signatures;
    au_plan;
    au_procedure;
    au_application_view;
    atomic_operations;
    token_types;
    generic_models;
    resource_types;
    types;
    native_resource_members;
    imported_resource_members;
    public_resource_members;
    deferred_native_resource_members;
    pending_declarations;
    available_layouts;
    take_declarations;
    modules;
    refs;
    primitives;
    functions;
    lifted;
    origins;
    ocaml_env;
    scoped_proofs;
    scoped_inputs;
    predicates;
    library_preds;
  } =
    decls
  in
  let* proofs = Program_proofs.run scopes decls in
  let {
    Program_proofs.checked_views;
    checked_resource_entries;
    logical_declarations;
    all_logical_functions;
    context_owners;
    proof_context;
    module_context;
    proof_context_for;
    proof_support;
    preds;
    spec_funcs;
    lemma_declarations;
    lemma_context;
  } =
    proofs
  in
  let* shaped = Program_structures.run scopes decls proofs in
  let {
    Program_structures.structures;
    structure_member_lists;
    view_fields;
    owner_destination;
    same_group;
    field_group;
    shared;
    generic_shared;
    shared_for_proof;
    body_shared;
    state_members;
    past_structures;
    pasts;
    past_returns;
    ghost_args;
  } =
    shaped
  in
  (* Each library's module, trusted: its abstract predicates, and its values, as functions
     without arguments, and functions, as procedures with their contracts. *)
  let* library_modules =
    all libraries ~f:(fun (lib : Library_modules.t) ->
        let l = loc Location.none in
        let* environment = Library_modules.environment source lib in
        let own_preds =
          List.filter_map library_preds ~f:(fun ((lib' : Library_modules.t), p, types) ->
              Option.some_if
                (String.equal lib'.library_name lib.library_name)
                ( p.pred_name.pid_str,
                  (lib.library_name ^ "." ^ p.pred_name.pid_str, types) ))
        in
        (* In the library's contracts, its predicates go by their own names. *)
        let own_inputs =
          List.filter_map own_preds ~f:(fun (local, (qualified, _)) ->
              Option.map
                (List.Assoc.find proof_support.predicate_inputs qualified
                   ~equal:String.equal) ~f:(fun inputs -> (local, inputs)))
        in
        let ctx =
          scoped_contract_context types ~refs ~primitives ~shared ~environment
            ~proof_support ~preds ~spec_funcs ~own_preds ~own_inputs origins
        in
        let* pred_members =
          all
            (List.filter library_preds ~f:(fun ((lib' : Library_modules.t), _, _) ->
                 String.equal lib'.library_name lib.library_name))
            ~f:(fun (_, (p : S.predicate), param_types) ->
              let* params =
                all (List.zip_exn p.pred_params param_types) ~f:(fun ((x, _), t) ->
                    let* typ = Datatypes.typ types ~at:x.S.pid_loc t in
                    Ok (t, R.Var.make ~loc:l (ident ~loc:l x.pid_str) typ))
              in
              (* Libraries share the program's predicate output convention. *)
              let* outputs = predicate_output_count types p param_types in
              let inputs, outputs = List.split_n params (List.length params - outputs) in
              let kind = if p.pred_persistent then R.Callable.Inv else R.Callable.Pred in
              Ok
                (R.Member.free
                   (R.Member.callable
                      (R.Callable.func ~loc:l ~kind ~formals:(List.map inputs ~f:snd)
                         ~returns:(List.map outputs ~f:snd)
                         (ident ~loc:l p.pred_name.pid_str)
                         None))))
        in
        let* contracts = interface_contracts lib.library in
        let* value_members =
          all lib.library.signature ~f:(fun (item : Parsetree.signature_item) ->
              match item.psig_desc with
              | Psig_value vd ->
                  let at = vd.pval_loc in
                  let x = vd.pval_name.txt in
                  let value = Env.find_value (Pdot (lib.library_path, x)) source.env in
                  let rec arrows (t : Types.type_expr) =
                    match Types.get_desc t with
                    | Tarrow (Nolabel, a, r, _) ->
                        let args, result = arrows r in
                        (Datatypes.expand types a :: args, result)
                    | Tpoly (t, []) -> arrows t
                    | _ -> ([], t)
                  in
                  let args, result = arrows value.val_type in
                  let contract =
                    Option.map (List.Assoc.find contracts x ~equal:String.equal) ~f:fst
                  in
                  let* member = library_function ctx ~at ~name:x ~args ~result contract in
                  Ok [ R.Member.free (R.Member.callable member) ]
              | Psig_type _ | Psig_attribute _ -> Ok []
              | _ -> unsupported item.psig_loc "This item of a library's interface")
        in
        Ok
          (R.Member.module_ ~loc:l
             (ident ~loc:l lib.library_name)
             (pred_members @ List.concat value_members)))
  in
  let prepare_view_operation (view : checked_view) operation =
    let signature = operation.operation_signature in
    let* () =
      check_adapter_shape ~at:signature.site.item_loc operation.operation_contract
    in
    let* raw_resources =
      all view.view_resources ~f:(fun (formal, resource) ->
          let environment =
            Source.annotation_env source formal.Module_inventory.site.environment
          in
          let* ts =
            all formal.declaration.pred_params ~f:(fun (id, pty) ->
                Source.ocaml_type environment ~at:id.S.pid_loc pty)
          in
          Ok (formal.declaration, resource.resource_backend, ts))
    in
    let own_preds =
      List.map raw_resources ~f:(fun (p, target, ts) ->
          (p.S.pred_name.pid_str, (target, ts)))
    in
    let* own_inputs =
      all raw_resources ~f:(fun (p, _, ts) ->
          let* count = implicit_parameter_count ~kind:"predicate" p.S.pred_params in
          Ok
            (Option.map count ~f:(fun count ->
                 (p.pred_name.pid_str, List.length ts - count))))
    in
    let* environment =
      Source.realize_signature_ghost_environment source
        ~substitution:view.view_binding.parameter_substitution
        (List.map view.view_binding.expected.signature_ghost_modules
           ~f:(fun (_, formal) -> formal.Module_inventory.ghost_declaration))
        (Source.annotation_env source signature.site.environment)
    in
    let ctx =
      scoped_contract_context view.view_types ~refs ~primitives ~shared ~environment
        ~proof_support:{ proof_support with strict_source_types = true }
        ~preds ~spec_funcs ~own_preds ~own_inputs:(List.filter_opt own_inputs) origins
    in
    let predicates q =
      let env =
        {
          ctx;
          data = ctx.given.types;
          funcs = ctx.given.spec_funcs;
          vars = [];
          var_types = [];
          logical_definition = false;
        }
      in
      Option.map
        (List.Assoc.find ctx.given.preds (logical_key env q) ~equal:String.equal)
        ~f:snd
    in
    let* () =
      match operation.operation_contract with
      | None -> Ok ()
      | Some contract ->
          let* () = Signature_contract.lowerable source signature ~environment contract in
          Signature_contract.check ~logical_types:source.logical_types ~restricted:true
            ~predicates ~environment source signature contract
    in
    let args, result =
      Signature_contract.arguments signature.declaration.val_val.val_type
    in
    let* () =
      if List.is_empty args then
        unsupported signature.site.item_loc
          "A non-function value in a checked module signature"
      else Ok ()
    in
    let* expected =
      prepare_callable ~validate:true ctx ~at:signature.site.item_loc ~args ~result
        operation.operation_contract
    in
    Ok (ctx, args, result, expected)
  in
  let publication_members = ref [] in
  let publications = ref [] in
  let checked_prepared = ref [] in
  let* adapter_members =
    all checked_operations ~f:(fun operation ->
        let binding = operation.operation_binding in
        let view =
          List.find_exn checked_views ~f:(fun view ->
              phys_equal view.view_binding binding)
        in
        let signature = operation.operation_signature in
        let at = binding.site.item_loc in
        let member = signature.declaration.val_name.txt in
        let actual_path = Path.Pdot (binding.actual_path, member) in
        let* ctx, args, result, expected = prepare_view_operation view operation in
        let* actual, actual_contract, actual_projection, actual_at, actual_name =
          match List.Assoc.find !checked_prepared actual_path ~equal:Path.same with
          | Some info -> Ok info
          | None -> (
              match
                List.find funcs ~f:(fun f ->
                    List.mem f.paths actual_path ~equal:Path.same)
              with
              | Some f ->
                  let preds, spec_funcs, proof_support =
                    proof_context ~current_procedure:(proc_name f)
                      (Proof_bindings.scope_for_location scoped_proofs f.loc)
                      preds spec_funcs proof_support
                  in
                  let* () = check_adapter_shape ~at:f.loc f.contract in
                  let* () =
                    if
                      (is_pure f && logical_contract f.contract)
                      || (not (List.is_empty f.captured))
                      || Option.is_some f.role
                    then
                      unsupported at
                        "A pure or lifted operation in a checked module binding"
                    else Ok ()
                  in
                  let actual_ctx =
                    spec_context types ~refs ~primitives ~shared ~ocaml_env:f.environment
                      ~proof_support ~preds ~spec_funcs origins
                  in
                  let actual_args =
                    List.filter_map f.params ~f:(fun p ->
                        match p.Typedtree.fp_kind with
                        | Tparam_pat pat -> Some pat.pat_type
                        | _ -> None)
                  in
                  let* prepared =
                    prepare_callable actual_ctx ~at:f.loc ~args:actual_args
                      ~result:f.body.exp_type f.contract
                  in
                  let* () =
                    if
                      (not
                         (List.is_empty
                            (Option.value
                               (List.Assoc.find pasts (proc_name f) ~equal:String.equal)
                               ~default:[])))
                      || not
                           (List.is_empty
                              (Option.value
                                 (List.Assoc.find past_returns (proc_name f)
                                    ~equal:String.equal)
                                 ~default:[]))
                    then unsupported at "A history contract in a checked module binding"
                    else Ok ()
                  in
                  let target =
                    if not (is_pure f) then proc_name f
                    else
                      match List.Assoc.find !publications f.id ~equal:Ident.same with
                      | Some publication -> publication
                      | None ->
                          let publication = fresh ("published_" ^ f.raven_name) in
                          let body =
                            forwarding_body actual_ctx ~at ~self:publication
                              ~target:(proc_name f) ~result:f.body.exp_type ~atomic:false
                              prepared
                          in
                          publications := (f.id, publication) :: !publications;
                          publication_members :=
                            ( binding,
                              prepared_member ~at ~name:publication (Some body) prepared
                            )
                            :: !publication_members;
                          publication
                  in
                  let projection =
                    List.fold all_resource_views ~init:Subst.identity
                      ~f:(fun projection resource ->
                        let path =
                          Path.Pdot (binding.actual_path, resource.Source.resource_name)
                        in
                        if
                          Path.same
                            (Proof_bindings.canonical_owner scoped_proofs
                               resource.resource_path)
                            (Proof_bindings.canonical_owner scoped_proofs path)
                        then Subst.add_module resource.resource_id path projection
                        else projection)
                  in
                  let projection =
                    List.fold types ~init:projection ~f:(fun projection data ->
                        match data.Datatypes.id with
                        | None -> projection
                        | Some id -> (
                            match
                              List.find data.paths ~f:(function
                                | Path.Pdot (parent, _) ->
                                    Path.same parent binding.actual_path
                                | _ -> false)
                            with
                            | None -> projection
                            | Some path -> Subst.add_type id path projection))
                  in
                  Ok (prepared, f.contract, projection, f.loc, target)
              | None ->
                  let library =
                    List.find libraries ~f:(fun lib ->
                        Path.same lib.Library_modules.library_path binding.actual_path)
                  in
                  begin match library with
                  | None ->
                      unsupported at
                        "A checked module argument without a supported operation contract"
                  | Some lib ->
                      let* contracts = interface_contracts lib.library in
                      let contract =
                        Option.map
                          (List.Assoc.find contracts member ~equal:String.equal)
                          ~f:fst
                      in
                      let* () = check_adapter_shape ~at contract in
                      let value = Env.find_value actual_path binding.site.environment in
                      let actual_args, actual_result =
                        Signature_contract.arguments value.val_type
                      in
                      let own_preds =
                        List.filter_map library_preds ~f:(fun (library, p, ts) ->
                            Option.some_if
                              (Path.same library.Library_modules.library_path
                                 lib.library_path)
                              ( p.S.pred_name.pid_str,
                                (library.library_name ^ "." ^ p.pred_name.pid_str, ts) ))
                      in
                      let own_inputs =
                        List.filter_map own_preds ~f:(fun (local, (target, _)) ->
                            Option.map
                              (List.Assoc.find proof_support.predicate_inputs target
                                 ~equal:String.equal) ~f:(fun count -> (local, count)))
                      in
                      let* environment = Library_modules.environment source lib in
                      let actual_ctx =
                        scoped_contract_context types ~refs ~primitives ~shared
                          ~environment ~proof_support ~preds ~spec_funcs ~own_preds
                          ~own_inputs origins
                      in
                      let* prepared =
                        prepare_callable actual_ctx ~at:value.val_loc ~args:actual_args
                          ~result:actual_result contract
                      in
                      Ok
                        ( prepared,
                          contract,
                          Subst.identity,
                          value.val_loc,
                          lib.library_name ^ "." ^ member )
                  end)
        in
        let* () =
          if
            Bool.equal
              (logical_contract actual_contract)
              (logical_contract operation.operation_contract)
          then Ok ()
          else
            error at
              "The module operation has a different ordinary or logically atomic \
               contract kind"
        in
        let expected_implicit = expected.prepared_implicit
        and actual_implicit = actual.prepared_implicit in
        let* () =
          if
            List.length expected_implicit = List.length actual_implicit
            && Poly.equal expected.prepared_roles actual.prepared_roles
          then Ok ()
          else
            unsupported at
              "Different implicit argument shapes in a checked module binding"
        in
        let* () =
          if
            List.for_all2_exn expected_implicit actual_implicit
              ~f:(fun (_, _, a, _, _) (_, _, b, _, _) ->
                Ctype.is_equal
                  (Source.annotation_env source binding.site.environment)
                  false
                  [ Subst.type_expr view.view_actual_substitution a ]
                  [
                    Subst.type_expr binding.parameter_substitution
                      (Subst.type_expr actual_projection b);
                  ])
          then Ok ()
          else error at "The module operation has different implicit argument types"
        in
        let* () =
          if
            List.exists
              (args @ [ result ]
              @ List.map expected_implicit ~f:(fun (_, _, t, _, _) -> t))
              ~f:(contains_atomic_token view.view_types)
          then unsupported at "Public atomic-update tokens in a checked module binding"
          else Ok ()
        in
        let body =
          forwarding_body ctx ~at ~self:operation.operation_name ~target:actual_name
            ~result
            ~atomic:(logical_contract operation.operation_contract)
            expected
        in
        let related =
          [
            (signature.site.item_loc, "The requested module operation");
            (actual_at, "The actual module operation");
          ]
        in
        List.iter
          [
            ( R.Diagnostic.Precondition,
              "The module argument's precondition is not provided by this view" );
            ( Postcondition,
              "The module argument does not establish this view's postcondition" );
            ( Commit,
              "The module argument does not establish this view's atomic postcondition" );
            ( Abortable_call,
              "This view's atomic update may not be restorable if the actual operation \
               aborts" );
          ]
          ~f:(fun (code, message) ->
            origins := { at; code; message; related } :: !origins);
        origins :=
          {
            at = { at with loc_start = at.loc_end };
            code = Postcondition;
            message = "The module argument does not establish this view's postcondition";
            related;
          }
          :: !origins;
        List.iter operation.operation_paths ~f:(fun path ->
            let projection =
              match path with
              | Path.Pdot (parent, _) -> checked_type_substitution binding parent
              | _ -> view.view_source_substitution
            in
            checked_prepared :=
              ( path,
                ( expected,
                  operation.operation_contract,
                  projection,
                  signature.site.item_loc,
                  operation.operation_name ) )
              :: !checked_prepared);
        Ok
          ( operation,
            expected,
            prepared_member ~at ~name:operation.operation_member (Some body) expected ))
  in
  let symbolic_view group owner =
    let view =
      List.find_exn checked_views ~f:(fun view ->
          phys_equal view.view_binding group.Generic_modules.representative.argument)
    in
    {
      view with
      view_types =
        Generic_modules.types group ~owner
        @ (let root =
             List.find_exn generics ~f:(fun root ->
                 String.equal root.Generic_modules.name group.name)
           in
           Option.value_map root.world ~default:[] ~f:(fun world ->
               List.concat_map (Generic_modules.parameter_groups root) ~f:(fun stage ->
                   Generic_modules.world_types stage ~owner:[ world ])))
        @ types;
      view_resources =
        List.map view.view_resources ~f:(fun (formal, resource) ->
            let stem =
              List.Assoc.find_exn group.resources
                formal.Module_inventory.declaration.pred_name.pid_str ~equal:String.equal
            in
            ( formal,
              {
                resource with
                resource_backend = String.concat ~sep:"." (owner @ [ stem ]);
              } ));
    }
  in
  let resource_members group view ~aliases =
    all view.view_resources ~f:(fun (formal, resource) ->
        let p = formal.Module_inventory.declaration in
        let l = loc p.pred_name.pid_loc in
        let environment = Source.annotation_env source formal.site.environment in
        let* parameter_types =
          all p.pred_params ~f:(fun (id, pty) ->
              Source.ocaml_type environment ~at:id.S.pid_loc pty)
        in
        let* vars =
          all (List.zip_exn p.pred_params parameter_types) ~f:(fun ((id, _), t) ->
              let* typ = Datatypes.typ view.view_types ~at:id.S.pid_loc t in
              Ok (R.Var.make ~loc:l (ident ~loc:l id.pid_str) typ))
        in
        let* outputs = predicate_output_count view.view_types p parameter_types in
        let formals, returns = List.split_n vars (List.length vars - outputs) in
        let stem =
          List.Assoc.find_exn group.Generic_modules.resources p.pred_name.pid_str
            ~equal:String.equal
        in
        let member =
          if aliases then
            let kind =
              if p.pred_persistent then R.Callable.Invariant else R.Callable.Predicate
            in
            R.Callable.resource_alias ~loc:l ~kind ~formals ~returns (ident ~loc:l stem)
              (qualified_name ~loc:l resource.resource_backend)
          else
            let kind = if p.pred_persistent then R.Callable.Inv else R.Callable.Pred in
            R.Callable.func ~loc:l ~kind ~formals ~returns (ident ~loc:l stem) None
        in
        Ok (R.Member.callable member))
  in
  let type_members group view ~aliases =
    let* members =
      all view.view_binding.expected.signature_types ~f:(fun (source, declaration) ->
          if
            aliases
            && (Option.is_some group.Generic_modules.world
               || Option.is_some declaration.Typedtree.typ_manifest)
          then Ok None
          else
            let at = declaration.Typedtree.typ_loc in
            let l = loc at in
            let* definition =
              if aliases then
                let t =
                  Btype.newgenty
                    (Tconstr (Path.Pident declaration.typ_id, [], ref Types.Mnil))
                in
                Result.map (Datatypes.typ view.view_types ~at t) ~f:Option.some
              else
                match (group.Generic_modules.world, declaration.typ_manifest) with
                | Some world, _ ->
                    let stem =
                      List.Assoc.find_exn group.types source ~equal:String.equal
                    in
                    Ok
                      (Some
                         (R.Type.named ~loc:l
                            (R.Name.make ~loc:l ~path:[ world ] stem)
                            []))
                | None, None -> Ok None
                | None, Some t ->
                    Result.map
                      (Datatypes.typ view.view_types ~at t.ctyp_type)
                      ~f:Option.some
            in
            let stem =
              List.Assoc.find_exn group.Generic_modules.types source ~equal:String.equal
            in
            Ok (Some (R.Member.type_ ~loc:l (ident ~loc:l stem) definition)))
    in
    Ok (List.filter_opt members)
  in
  let ghost_contract_members ?(carrier_interface = fun _ -> None) ~aliases ~implementation
      ~scope ~path ~at signature =
    all signature.Module_inventory.signature_ghost_modules ~f:(fun (member, formal) ->
        let declaration = formal.Module_inventory.ghost_declaration in
        let at = declaration.S.ghost_module_name.pid_loc in
        let l = loc at in
        let* signatures = Proof_library.signatures at in
        let* interface =
          match
            Proof_library.find signatures
              (Proof_library.path_of_qualid declaration.ghost_module_interface)
          with
          | Some interface
            when interface.interface
                 && Proof_library.is_resource_algebra signatures interface ->
              Ok interface
          | Some _ | None ->
              error at "An abstract proof module must name a resource algebra interface"
        in
        let interface_name =
          Option.value (carrier_interface member)
            ~default:(qualified_name ~loc:l (String.concat ~sep:"." interface.path))
        in
        if not aliases then
          Ok (R.Member.instance ~loc:l (ident ~loc:l member) interface_name)
        else
          let wanted =
            Proof_bindings.canonical_owner scoped_proofs (Path.Pdot (path, member))
          in
          match
            List.find all_resources ~f:(fun resource ->
                Source.resource_has_path resource wanted
                || Path.same wanted
                     (Proof_bindings.canonical_owner scoped_proofs
                        resource.Source.resource_path))
          with
          | None -> error at ("The actual module does not declare proof module " ^ member)
          | Some resource ->
              let resource =
                if implementation then resource else resource_view ~scope resource
              in
              if
                not
                  (List.exists resource.resource_interfaces
                     ~f:(List.equal String.equal interface.path))
              then
                error at
                  ("The proof module " ^ member ^ " does not implement "
                  ^ String.concat ~sep:"." interface.path)
              else
                Ok
                  (match carrier_interface member with
                  | None ->
                      R.Member.alias ~loc:l (ident ~loc:l member)
                        (qualified_name ~loc:l resource.resource_backend)
                  | Some typ ->
                      R.Member.checked_view ~loc:l ~typ (ident ~loc:l member)
                        (qualified_name ~loc:l resource.resource_backend)))
  in
  let ghost_module_members ~aliases (binding : Module_inventory.checked_binding) =
    let carrier_interface member =
      Option.bind (Generic_modules.application_for_binding generics binding)
        ~f:(fun (stage, application) ->
          Option.map stage.world ~f:(fun world ->
              let owner = if aliases then application.world else world in
              qualified_name ~loc:(loc binding.site.item_loc)
                (owner ^ "." ^ Generic_modules.algebra_name stage member)))
    in
    ghost_contract_members ~carrier_interface ~aliases ~implementation:false
      ~scope:(Proof_bindings.scope_for_location scoped_proofs binding.site.item_loc)
      ~path:binding.actual_path ~at:binding.site.item_loc binding.expected
  in
  let* _ =
    all inventory.constraints ~f:(fun constraint_ ->
        match
          Option.first_some constraint_.Module_inventory.result_owner constraint_.owner
        with
        | None -> Ok []
        | Some path ->
            ghost_contract_members ~aliases:true ~implementation:true ~scope:None ~path
              ~at:constraint_.at constraint_.signature)
  in
  let* _ =
    all inventory.bindings ~f:(fun binding -> ghost_module_members ~aliases:true binding)
  in
  let* generic_interfaces =
    all generics ~f:(fun owner ->
        all (Generic_modules.parameter_groups owner) ~f:(fun group ->
            let view = symbolic_view group (String.split group.interface ~on:'.') in
            let* types = type_members group view ~aliases:false in
            let* resources = resource_members group view ~aliases:false in
            let* ghost_modules =
              ghost_module_members ~aliases:false group.representative.argument
            in
            let* operations =
              all checked_operations ~f:(fun operation ->
                  if
                    not
                      (phys_equal operation.operation_binding
                         group.representative.argument)
                  then Ok None
                  else
                    let* _, _, _, prepared = prepare_view_operation view operation in
                    Ok
                      (Some
                         (R.Member.callable
                            (prepared_member
                               ~at:operation.operation_signature.site.item_loc
                               ~name:operation.operation_member None prepared))))
            in
            let l = loc group.representative.argument.site.item_loc in
            let carriers =
              Option.value_map group.world ~default:[] ~f:(fun world ->
                  List.map group.representative.argument.expected.signature_ghost_modules
                    ~f:(fun (member, _) ->
                      R.Member.module_ ~loc:l ~interface:true
                        ~implements:
                          [ (qualified_name ~loc:l "Library.ResourceAlgebra", []) ]
                        (ident ~loc:l (Generic_modules.algebra_name group member))
                        [
                          R.Member.type_ ~loc:l ~rep:true (ident ~loc:l "T")
                            (Some
                               (R.Type.named ~loc:l
                                  (qualified_name ~loc:l
                                     (world ^ "."
                                     ^ Generic_modules.carrier_name group member))
                                  []));
                        ]))
            in
            Ok
              (carriers
              @ [
                  R.Member.module_ ~loc:l ~interface:true
                    (ident ~loc:l (Qualified_name.of_string group.interface).name)
                    (types @ resources @ ghost_modules @ List.filter_opt operations);
                ])))
    |> Result.map ~f:(List.map ~f:List.concat)
  in
  let* checked_module_members =
    all checked_modules ~f:(fun view ->
        let at = view.Checked_modules.binding.site.item_loc in
        let l = loc at in
        let members =
          List.filter adapter_members ~f:(fun (operation, _, _) ->
              phys_equal operation.operation_binding view.binding)
        in
        match (view.grouped, view.target) with
        | false, _ ->
            Ok (List.map members ~f:(fun (_, _, member) -> R.Member.callable member))
        | true, Some target ->
            Ok
              [
                R.Member.checked_view ~loc:l
                  ~typ:(qualified_name ~loc:l view.interface)
                  (ident ~loc:l view.name) (name ~loc:l target);
              ]
        | true, None ->
            let declarations =
              List.map members ~f:(fun (operation, prepared, _) ->
                  R.Member.callable
                    (prepared_member ~at:operation.operation_signature.site.item_loc
                       ~name:operation.operation_member None prepared))
            in
            let* prefix, aliases =
              match Generic_modules.application_for_binding generics view.binding with
              | None ->
                  Ok
                    ( [
                        R.Member.module_ ~loc:l ~interface:true
                          (ident ~loc:l view.interface) declarations;
                      ],
                      [] )
              | Some (group, _) ->
                  let concrete =
                    List.find_exn checked_views ~f:(fun checked ->
                        phys_equal checked.view_binding view.binding)
                  in
                  let* types = type_members group concrete ~aliases:true in
                  let* resources = resource_members group concrete ~aliases:true in
                  let* ghost_modules = ghost_module_members ~aliases:true view.binding in
                  Ok ([], types @ resources @ ghost_modules)
            in
            Ok
              (prefix
              @ [
                  R.Member.module_ ~loc:l
                    ~implements:[ (qualified_name ~loc:l view.interface, []) ]
                    (ident ~loc:l view.name)
                    (aliases
                    @ List.map members ~f:(fun (_, _, member) -> R.Member.callable member)
                    );
                ]))
  in
  (* The checks that the actions keep the histories' orders. *)
  let* action_check_lists =
    all structures ~f:(fun st ->
        let preds, spec_funcs, proof_support =
          proof_context_for ~preds ~spec_funcs ~proof_support st.invariant
        in
        let* members =
          action_checks
            (spec_context types ~refs ~primitives
               ~shared:(shared_for_proof st.invariant)
               ~ocaml_env:st.environment ~preds ~spec_funcs ~proof_support origins)
            st
        in
        Ok (st, members))
  in
  let* pending_member_lists =
    all structures ~f:(fun st ->
        let* members =
          all st.pendings ~f:(fun p ->
              match List.find funcs ~f:(fun f -> Ident.same f.id p.helped) with
              | Some helped ->
                  let preds, spec_funcs, proof_support =
                    proof_context_for ~preds ~spec_funcs ~proof_support st.invariant
                  in
                  pending_members
                    (spec_context types ~refs ~primitives
                       ~shared:(shared_for_proof st.invariant)
                       ~ocaml_env:st.environment ~preds ~spec_funcs ~proof_support origins)
                    st p helped
                    ~helped_proc:
                      (match owner_destination st.invariant with
                      | Module_context.Flat -> proc_name helped
                      | Module_context.Worker _ -> body_proc_name helped)
              | None ->
                  error st.at
                    (Printf.sprintf "There is no function %s to help"
                       (Ident.name p.helped)))
        in
        Ok (st, List.concat members))
  in
  let* pred_members =
    all predicates ~f:(fun (at, p, def, param_types) ->
        let preds, spec_funcs, proof_support =
          proof_context_for ~preds ~spec_funcs ~proof_support p.pred_name.pid_str
        in
        predicate types ~refs ~primitives
          ~shared:(shared_for_proof p.pred_name.pid_str)
          ~ocaml_env:(declaration_environment p.pred_name.pid_str)
          ~preds ~spec_funcs ~proof_support
          ?declaration_name:(definition_member_name p.pred_name.pid_str)
          origins ~at ~structures p def param_types)
  in
  let predicate_bodies =
    List.filter_map predicates ~f:(fun (_, p, definition, _) ->
        match definition with
        | (Body body | Direct_invariant body)
          when Option.is_none (scoped_binding p.pred_name.pid_str) ->
            Some
              ( p.S.pred_name.pid_str,
                { definition = body; environment = ocaml_env; project_type = Fn.id } )
        | Body _ | Direct_invariant _ -> None
        | Invariant _ | View _ -> None)
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        match binding.kind with
        | Predicate (_, Plain body)
          when binding.exported && not (Proof_bindings.opaque scoped_proofs binding) ->
            Some
              ( binding.public_key,
                {
                  definition = body;
                  environment = binding.environment;
                  project_type = Proof_bindings.public_type scoped_proofs;
                } )
        | _ -> None)
  in
  let body_contexts ?at scope =
    let owners = context_owners at in
    let environment =
      Option.value_map scope ~default:source.env ~f:(fun scope ->
          Source.annotation_env source scope.Proof_scopes.environment)
    in
    let project = Proof_bindings.context_type scoped_proofs ~environment in
    let predicate_bodies =
      List.filter_map scoped_proofs.bindings ~f:(fun binding ->
          match binding.kind with
          | Predicate (_, Plain body)
            when Proof_bindings.visible scoped_proofs ~scope binding
                 && not (Proof_bindings.opaque_at scoped_proofs ~scope binding) ->
              Some
                ( binding.public_key,
                  {
                    definition = body;
                    environment = binding.environment;
                    project_type = Proof_bindings.public_type scoped_proofs;
                  } )
          | _ -> None)
      @ predicate_bodies
    in
    let predicate_bodies =
      List.map predicate_bodies ~f:(fun (key, body) ->
          (key, { body with project_type = (fun ty -> project (body.project_type ty)) }))
    in
    let predicate_bodies =
      List.filter_map scoped_proofs.applications ~f:(fun view ->
          match view.source.kind with
          | Predicate (_, Plain body)
            when Proof_bindings.application_visible ~owners scoped_proofs ~scope view
                 && not
                      (Proof_bindings.application_opaque ~owners scoped_proofs ~scope view)
            ->
              Some
                ( view.key,
                  {
                    definition = body;
                    environment = view.source.environment;
                    project_type = (fun ty -> project (view.project_type ty));
                  } )
          | _ -> None)
      @ predicate_bodies
    in
    List.filter_map (Proof_bindings.private_bindings scoped_proofs ~scope)
      ~f:(fun binding ->
        match binding.kind with
        | Predicate (_, Plain body) ->
            Some
              ( binding.backend,
                {
                  definition = body;
                  environment = binding.environment;
                  project_type = Fn.id;
                } )
        | _ -> None)
    @ predicate_bodies
  in
  let module_lemmas context ~project lemmas =
    List.map lemmas ~f:(fun (key, signature) ->
        let backend =
          match scoped_binding signature.lemma_raven with
          | Some binding when Module_context.contains context binding ->
              Module_context.member context binding.backend
          | _ -> signature.lemma_raven
        in
        ( key,
          {
            signature with
            lemma_raven = backend;
            lemma_inputs = List.map signature.lemma_inputs ~f:project;
            lemma_outputs = List.map signature.lemma_outputs ~f:project;
          } ))
  in
  let* lemma_members =
    all lemma_declarations ~f:(fun declaration ->
        let declaration_name = (Proof_scopes.name declaration).pid_str in
        let scope = declaration_scope declaration_name in
        let preds, spec_funcs, proof_support =
          proof_context_for ~preds ~spec_funcs ~proof_support declaration_name
        in
        let lemmas = lemma_context scope in
        let lemmas =
          module_lemmas (declaration_context declaration_name) ~project:Fn.id lemmas
        in
        proof_lemma types ~refs ~primitives ~shared
          ~ocaml_env:(declaration_environment declaration_name)
          ~preds ~spec_funcs ~proof_lemmas:lemmas ~proof_support
          ~predicate_bodies:(body_contexts scope)
          ?member_name:(definition_member_name declaration_name)
          origins declaration)
  in
  let* logical_members =
    all
      (List.mapi logical_declarations ~f:(fun i declaration -> (i, declaration)))
      ~f:(fun (i, declaration) ->
        let declaration_name = (Proof_scopes.name declaration).pid_str in
        let scope = declaration_scope declaration_name in
        let preds, spec_funcs, proof_support =
          proof_context_for ~preds ~spec_funcs ~proof_support declaration_name
        in
        let previous =
          List.map (List.take logical_declarations i) ~f:(fun declaration ->
              (Proof_scopes.name declaration).pid_str)
        in
        let implementation_key backend =
          Option.value
            (List.find_map scoped_proofs.bindings ~f:(fun binding ->
                 Option.some_if
                   (Option.equal String.equal (definition_target binding) (Some backend))
                   binding.backend))
            ~default:
              (Option.value
                 (List.find_map scoped_proofs.applications ~f:(fun view ->
                      Option.some_if
                        (String.equal view.backend backend)
                        view.source.backend))
                 ~default:
                   (Option.value
                      (List.find_map scoped_proofs.bindings ~f:(fun binding ->
                           Option.bind (proof_worker binding.backend) ~f:(fun plan ->
                               Option.some_if
                                 (String.equal
                                    (Generic_proofs.member plan binding.backend)
                                    backend)
                                 binding.backend)))
                      ~default:backend))
        in
        let available signature =
          List.mem previous (implementation_key signature.lemma_raven) ~equal:String.equal
        in
        let logical_functions =
          List.filter proof_support.logical_functions ~f:(fun (_, signature) ->
              available signature)
        in
        let spec_funcs =
          List.filter spec_funcs ~f:(fun (key, _) ->
              match
                List.Assoc.find proof_support.logical_functions key ~equal:String.equal
              with
              | None -> true
              | Some signature -> available signature)
        in
        let* () =
          match declaration with
          | S.Proof_function { function_params; function_body; _ } ->
              let environment = declaration_environment declaration_name in
              let bound = List.map function_params ~f:(fun (id, _) -> id.S.pid_str) in
              Result.all_unit
                (List.map (term_references bound function_body) ~f:(fun q ->
                     let key =
                       Option.value
                         (Proof_bindings.resolve scoped_proofs ~scope ~environment q)
                         ~default:(qualid_key q)
                     in
                     let key =
                       Option.value
                         (Proof_bindings.canonical_key scoped_proofs key)
                         ~default:key
                     in
                     if
                       List.Assoc.mem all_logical_functions key ~equal:String.equal
                       && not (List.mem previous key ~equal:String.equal)
                     then
                       error (S.qualid_loc q)
                         "A logical function can only call earlier logical definitions"
                     else Ok ()))
          | _ -> Ok ()
        in
        proof_function types ~refs ~primitives ~shared
          ~ocaml_env:(declaration_environment declaration_name)
          ~preds ~spec_funcs
          ~proof_support:{ proof_support with logical_functions }
          ?member_name:(definition_member_name declaration_name)
          ~as_value:
            (match declaration with
            | S.Proof_function { function_params = []; _ } -> true
            | _ -> false)
          origins declaration)
  in
  let pure_functions =
    Path_bindings.of_list
      (List.concat_map pure ~f:(fun f ->
           List.map f.paths ~f:(fun path -> (path, pure_name f))))
  in
  let* runtime_contexts =
    all runtime_destinations ~f:(fun destination ->
        let groups = Module_context.groups destination in
        let namespace = Module_context.namespace destination in
        let* layouts =
          all groups ~f:(fun group ->
              Result_layouts.symbolic layouts group ~owner:(namespace @ [ "Layout" ]))
        in
        let body_types =
          List.concat layouts
          @ List.concat_map groups ~f:(fun group ->
              Generic_modules.worker_types group ~owner:namespace)
          @ types
        in
        let stages = List.concat_map groups ~f:Generic_modules.parameter_groups in
        let predicate_overrides =
          List.filter_map checked_resource_entries ~f:(fun (path, key, _, ts) ->
              match path with
              | Path.Pdot (parent, member) ->
                  List.find_map stages ~f:(fun stage ->
                      if
                        List.mem stage.representative.argument.paths parent
                          ~equal:Path.same
                      then
                        Option.map
                          (List.Assoc.find stage.resources member ~equal:String.equal)
                          ~f:(fun stem ->
                            ( key,
                              ( String.concat ~sep:"."
                                  (namespace @ [ stage.parameter; stem ]),
                                ts ) ))
                      else None)
              | _ -> None)
        in
        let representatives =
          List.filter funcs ~f:(fun f ->
              List.exists groups ~f:(fun group ->
                  List.exists group.representative.body_members ~f:(fun (_, id) ->
                      Ident.same id f.id)))
        in
        let map_functions ?(only_pure = false) initial target =
          let selected =
            if only_pure then List.filter representatives ~f:is_pure else representatives
          in
          List.fold selected ~init:initial ~f:(fun mappings f ->
              List.fold f.paths ~init:mappings ~f:(fun mappings path ->
                  Path_bindings.add mappings path (target f)))
        in
        let body_functions = map_functions functions body_proc_name in
        let body_functions =
          List.fold checked_operations ~init:body_functions ~f:(fun mappings operation ->
              match
                List.find stages ~f:(fun stage ->
                    phys_equal operation.operation_binding stage.representative.argument)
              with
              | None -> mappings
              | Some stage ->
                  List.fold operation.operation_paths ~init:mappings
                    ~f:(fun mappings path ->
                      Path_bindings.add mappings path
                        (String.concat ~sep:"."
                           (namespace @ [ stage.parameter; operation.operation_member ]))))
        in
        Ok
          ( destination,
            {
              body_types;
              predicate_overrides;
              calls = body_functions;
              pure_calls = map_functions ~only_pure:true pure_functions body_pure_name;
              representatives;
              logical_calls =
                map_functions ~only_pure:true proof_support.runtime_functions
                  body_pure_reference;
            } ))
  in
  let body_context f =
    let context = body_module_context f in
    let preds, spec_funcs, proof_support =
      module_context context ~projection:context.projection
        (proof_context ~current_procedure:(proc_name f) ~at:f.loc (Some context.scope)
           preds spec_funcs proof_support)
    in
    let plan =
      List.Assoc.find_exn runtime_contexts (body_destination f)
        ~equal:Module_context.same_destination
    in
    let body_spec_funcs =
      List.map spec_funcs ~f:(fun (source, target) ->
          let target =
            match List.Assoc.find plan.predicate_overrides source ~equal:String.equal with
            | Some (target, _) -> target
            | None ->
                Option.value_map
                  (List.find plan.representatives ~f:(fun f ->
                       String.equal target (pure_name f)))
                  ~default:target ~f:body_pure_name
          in
          (source, target))
    in
    let body_proof_support =
      { proof_support with runtime_functions = plan.logical_calls }
    in
    ( plan.body_types,
      plan.predicate_overrides @ preds,
      plan.calls,
      plan.pure_calls,
      body_spec_funcs,
      body_proof_support )
  in
  let runtime_primitives =
    List.map runtime_destinations ~f:(fun destination ->
        ( destination,
          if Module_context.same_destination destination Module_context.Flat then
            primitives
          else ref [] ))
  in
  let body_primitives f =
    let destination = body_destination f in
    ( List.Assoc.find_exn runtime_primitives destination
        ~equal:Module_context.same_destination,
      Module_context.namespace destination )
  in
  let body_environment f =
    let context = body_module_context f in
    let* environment =
      List.fold_result (Module_context.parameter_pairs context) ~init:f.environment
        ~f:(fun environment (original, target) ->
          Source.project_ghost_parameter source ~original ~target environment)
    in
    let environment =
      List.fold (Module_context.runtime_pairs context) ~init:environment
        ~f:(fun environment (original, target) ->
          let declaration =
            {
              original.Typedtree.typ_type with
              type_kind = Types.Type_abstract Types.Definition;
              type_manifest = Some (Ctype.newconstr (Path.Pident target.typ_id) []);
              type_private = Asttypes.Public;
            }
          in
          Env.add_type ~check:false original.typ_id declaration environment)
    in
    if List.is_empty context.parameters then Ok environment
    else Ok (Source.annotation_env ~at:f.loc source environment)
  in
  let* pure_funcs =
    all pure ~f:(fun f ->
        match body_owner f with
        | Some (_, false) -> Ok None
        | _ ->
            let* environment = body_environment f in
            let f = { f with environment } in
            let data, predicates, _, pure_functions, spec_funcs, proof_support =
              body_context f
            in
            let declaration_name =
              Module_context.local_name (body_destination f) (body_pure_name f)
            in
            let primitives, primitive_namespace = body_primitives f in
            let* member =
              func data ~refs ~primitives ~shared:(body_shared f) ~ocaml_env:f.environment
                ~preds:predicates ~funcs:pure_functions ~spec_funcs ~proof_support
                ~declaration_name ~primitive_namespace origins f
            in
            Ok (Some (f, member)))
  in
  let* procs =
    all funcs ~f:(fun f ->
        match body_owner f with
        | Some (_, false) -> Ok None
        | _ ->
            let* environment = body_environment f in
            let f = { f with environment } in
            let data, predicates, functions, _, spec_funcs, proof_support =
              body_context f
            in
            let declaration_name =
              Module_context.local_name (body_destination f) (body_proc_name f)
            in
            let primitives, primitive_namespace = body_primitives f in
            let* member =
              let given =
                {
                  (declaration_inputs data ~shared:(body_shared f) ~env:f.environment
                     ~preds:predicates ~spec_funcs ~proof_support ~primitive_namespace ())
                  with
                  functions;
                  lifted;
                  pasts;
                  past_returns;
                  ghost_args;
                  procedure_signatures;
                  libraries = library_paths libraries;
                  annotations;
                  proof_lemmas =
                    (let context = body_module_context f in
                     module_lemmas context
                       ~project:(Module_context.project_type context)
                       (lemma_context ~at:f.loc (Some context.scope)));
                  predicate_bodies =
                    (let context = body_module_context f in
                     List.map (body_contexts ~at:f.loc (Some context.scope))
                       ~f:(fun (key, body) ->
                         ( key,
                           {
                             body with
                             project_type =
                               (fun typ ->
                                 Module_context.project_type context
                                   (body.project_type typ));
                           } )));
                  access_proofs;
                  return_proofs;
                  initializations;
                  linearizations;
                }
              in
              proc ~given ~collected:{ refs; primitives; origins }
                ~past_structures:(past_structures ~symbolic:true f)
                ~proc_name:(body_proc_name f) ~pure:(is_pure f) ~declaration_name
                ~pure_name:(body_pure_reference f) f
            in
            Ok (Some (f, member)))
  in
  let pure_funcs = List.filter_opt pure_funcs and procs = List.filter_opt procs in
  let owned destination members =
    List.filter members ~f:(fun (f, _) ->
        Module_context.same_destination destination (body_destination f))
  in
  let procedure_member (f, member) =
    if f.trusted then R.Member.free (R.Member.callable member)
    else R.Member.callable member
  in
  let predicate_members =
    List.zip_exn
      (List.map predicates ~f:(fun (_, p, _, _) -> p.S.pred_name.pid_str))
      pred_members
  in
  let proof_lemma_members =
    List.zip_exn
      (List.map lemma_declarations ~f:(fun d -> (Proof_scopes.name d).pid_str))
      lemma_members
  in
  let logical_members =
    List.zip_exn
      (List.map logical_declarations ~f:(fun d -> (Proof_scopes.name d).pid_str))
      logical_members
  in
  let proof_members =
    List.map (predicate_members @ proof_lemma_members) ~f:(fun (name, member) ->
        (name, R.Member.callable member))
    @ logical_members
  in
  let* definition_modules =
    all
      (List.filter source.proof_resources ~f:(fun resource ->
           resource.Source.resource_definition
           && Option.is_none resource.resource_application))
      ~f:(fun resource ->
        let at = resource.resource_at in
        let l = loc at in
        let* backend, representation =
          match (implementation resource, resource.resource_representation) with
          | Some backend, Some representation -> Ok (backend, representation)
          | _ -> error at "Missing resource algebra representation"
        in
        let* representation = Datatypes.typ types ~at representation in
        let carrier =
          R.Member.type_ ~loc:l ~rep:true (ident ~loc:l "T") (Some representation)
        in
        let members =
          List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
              Option.bind
                (List.find scoped_proofs.bindings ~f:(fun binding ->
                     Ident.same binding.entry.id entry.id
                     && (match binding.kind with Function _ -> true | _ -> false)
                     && Option.exists (definition_resource binding.entry.scope)
                          ~f:(fun owner ->
                            Ident.same owner.resource_id resource.resource_id)))
                ~f:(fun binding ->
                  List.Assoc.find proof_members binding.backend ~equal:String.equal))
        in
        let interface =
          qualified_name ~loc:l (String.concat ~sep:"." resource.resource_functor)
        in
        Ok
          ( resource,
            R.Member.module_ ~loc:l
              ~implements:[ (interface, []) ]
              (ident ~loc:l backend) (carrier :: members) ))
  in
  let definition_proof_modules =
    List.filter_map source.proof_resources ~f:(fun resource ->
        if
          (not resource.resource_definition)
          || Option.is_some resource.resource_application
        then None
        else
          Option.bind (proof_implementation resource) ~f:(fun backend ->
              let members =
                List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
                    Option.bind
                      (List.find scoped_proofs.bindings ~f:(fun binding ->
                           Ident.same binding.entry.id entry.id
                           && (match binding.kind with
                             | Predicate _ | Lemma _ -> true
                             | _ -> false)
                           && Option.exists (definition_resource binding.entry.scope)
                                ~f:(fun owner ->
                                  Ident.same owner.resource_id resource.resource_id)))
                      ~f:(fun binding ->
                        List.Assoc.find proof_members binding.backend ~equal:String.equal))
              in
              Option.some_if
                (not (List.is_empty members))
                ( resource,
                  R.Member.module_ ~loc:(loc resource.resource_at)
                    (ident ~loc:(loc resource.resource_at) backend)
                    members )))
  in
  let emitted_proofs destination members =
    List.filter_map members ~f:(fun (name, member) ->
        Option.some_if
          (Module_context.same_destination (owner_destination name) destination
          && Option.is_none (Option.bind (scoped_binding name) ~f:definition_target))
          member)
  in
  let emitted_assets destination members =
    List.filter_map members ~f:(fun (resource, member) ->
        Option.some_if
          (Module_context.emits_owner module_contexts ~destination
             resource.Source.resource_scope)
          member)
  in
  let emitted_fields destination fields =
    List.filter_map fields ~f:(fun (field, member) ->
        Option.some_if
          (Module_context.emits_owner module_contexts ~destination
             field.Source.field_scope)
          member)
  in
  let* explicit_fields =
    all source.proof_fields ~f:(fun field ->
        let l = loc field.Source.field_at in
        let* value_type =
          match field.field_resource with
          | None ->
              begin match
                List.find all_resource_views ~f:(fun resource ->
                    resource.resource_is_ra
                    && same_named_type field.field_value resource.resource_type)
              with
              | None -> Datatypes.typ types ~at:field.field_at field.field_value
              | Some resource ->
                  Ok
                    (R.Type.named ~loc:l
                       (qualified_name ~loc:l resource.resource_backend)
                       [])
              end
          | Some owner ->
              begin match
                List.find all_resource_views ~f:(fun resource ->
                    Source.resource_has_path resource owner)
              with
              | None -> error field.field_at "Unknown resource algebra for field"
              | Some resource ->
                  let private_representation =
                    resource.resource_definition
                    && Option.exists resource.resource_representation ~f:(fun rep ->
                        same_named_type field.field_value rep)
                  in
                  let* backend =
                    if private_representation then
                      match implementation resource with
                      | Some backend -> Ok backend
                      | None ->
                          error field.field_at "Missing resource algebra implementation"
                    else Ok resource.resource_backend
                  in
                  if resource.resource_is_ra then
                    Ok (R.Type.named ~loc:l (qualified_name ~loc:l backend) [])
                  else error field.field_at "The field resource is not a resource algebra"
              end
        in
        Ok
          ( field,
            Datatypes.field_member ~ghost:true types ~loc:l
              (Qualified_name.of_string (ghost_field_name field)).name value_type
              field.field_value ))
  in
  let emit_context_members destination ~at ~representations ~native_resources
      ~applications ~late_members =
    let group = List.hd (Module_context.groups destination) in
    let ghost_fields =
      List.filter_map view_fields ~f:(fun (_, (field, typ, init)) ->
          Option.some_if
            (Option.is_none init && same_group (field_group field) group)
            (R.Member.field ~loc:at ~ghost:true
               (ident ~loc:at (Module_context.local_name destination field))
               typ))
    in
    let primitive_members =
      !(List.Assoc.find_exn runtime_primitives destination
          ~equal:Module_context.same_destination)
      |> List.map ~f:snd
    in
    let stages =
      match destination with
      | Module_context.Flat ->
          [
            `Representations;
            `Definitions;
            `Native_resources;
            `Public_resources;
            `Applications;
            `View_fields;
            `Fields;
            `Proof_definitions;
            `State;
            `Late_members;
            `Primitives;
            `Predicates;
            `Pure_functions;
            `Lemmas;
            `Logical_functions;
            `Procedures;
          ]
      | Module_context.Worker _ ->
          [
            `Primitives;
            `Pure_functions;
            `Representations;
            `Definitions;
            `Native_resources;
            `Public_resources;
            `Applications;
            `Fields;
            `State;
            `View_fields;
            `Proof_definitions;
            `Late_members;
            `Predicates;
            `Lemmas;
            `Logical_functions;
            `Procedures;
          ]
    in
    List.concat_map stages ~f:(function
      | `Representations -> representations
      | `Definitions -> emitted_assets destination definition_modules
      | `Native_resources -> native_resources
      | `Public_resources -> emitted_assets destination public_resource_members
      | `Applications -> applications
      | `View_fields -> ghost_fields
      | `Fields -> emitted_fields destination explicit_fields
      | `Proof_definitions -> emitted_assets destination definition_proof_modules
      | `State ->
          state_members group structure_member_lists
          @ state_members group pending_member_lists
          @ state_members group action_check_lists
      | `Late_members -> late_members
      | `Primitives -> primitive_members
      | `Predicates ->
          List.map (emitted_proofs destination predicate_members) ~f:R.Member.callable
      | `Pure_functions ->
          List.map (owned destination pure_funcs) ~f:(fun (_, member) ->
              R.Member.callable member)
      | `Lemmas ->
          List.map (emitted_proofs destination proof_lemma_members) ~f:R.Member.callable
      | `Logical_functions -> emitted_proofs destination logical_members
      | `Procedures -> List.map (owned destination procs) ~f:procedure_member)
  in
  let* generic_implementations =
    all generics ~f:(fun group ->
        let l = loc group.representative.template.mod_loc in
        let q = qualified_name ~loc:l in
        let* ra_data =
          all
            (List.filter_map private_ra_types ~f:(fun (plan, data) ->
                 Option.some_if (phys_equal plan.Generic_proofs.group group) data))
            ~f:(Datatypes.member types)
        in
        let destination = Module_context.Worker group in
        let native_resources =
          List.filter_map native_resource_members ~f:(fun (backend, member) ->
              Option.bind
                (List.find source.proof_resources ~f:(fun resource ->
                     String.equal backend resource.Source.resource_backend))
                ~f:(fun resource ->
                  Option.some_if
                    (Module_context.emits_owner module_contexts ~destination
                       resource.resource_scope)
                    member))
        in
        let members =
          emit_context_members destination ~at:l ~representations:ra_data
            ~native_resources ~applications:[] ~late_members:[]
        in
        let worker =
          R.Member.module_ ~loc:l
            ~params:
              (List.map (Generic_modules.parameter_groups group) ~f:(fun stage ->
                   (ident ~loc:l stage.parameter, q stage.interface))
              @
              if Option.is_some group.world then
                [ (ident ~loc:l "Layout", q (Option.value_exn group.world ^ ".Shape")) ]
              else [])
            (ident ~loc:l (Qualified_name.of_string group.name).name)
            members
        in
        match group.world with
        | None -> Ok worker
        | Some world ->
            let* layout_types =
              Result_layouts.symbolic layouts group ~owner:[ world; "Shape" ]
            in
            let proof_plan =
              List.find generic_proofs ~f:(fun plan ->
                  phys_equal plan.Generic_proofs.group group)
            in
            let model_types =
              Option.value_map proof_plan ~default:[] ~f:(fun plan ->
                  Generic_proofs.symbolic_models source plan ~owner:[ world; "Shape" ])
            in
            let parameter_types =
              Option.value_map proof_plan ~default:[] ~f:(fun plan ->
                  Generic_proofs.parameter_types ~world:true plan ~owner:(fun _ ->
                      [ world ]))
            in
            let layout_types = layout_types @ model_types in
            let environment =
              layout_types @ parameter_types
              @ List.concat_map (Generic_modules.parameter_groups group) ~f:(fun stage ->
                  Generic_modules.world_types stage ~owner:[ world ])
              @ types
            in
            let* data_members =
              all
                (List.filter layout_types ~f:(fun d -> Option.is_none d.Datatypes.heap))
                ~f:(Datatypes.member environment)
            in
            let* fields =
              all
                (List.concat_map layout_types ~f:(fun d ->
                     List.map (Option.value d.Datatypes.heap ~default:[]) ~f:(fun field ->
                         (d, field))))
                ~f:(fun (d, field) ->
                  let* typ =
                    Datatypes.typ environment ~at:d.Datatypes.at field.Datatypes.typ
                  in
                  let leaf = (Qualified_name.of_string field.raven_field).name in
                  Ok (Datatypes.field_member environment ~loc:l leaf typ field.typ))
            in
            let projection =
              Option.value_map proof_plan ~default:Subst.identity
                ~f:Generic_proofs.projection
            in
            let field_contexts =
              (String.split group.name ~on:'.' @ [ "Layout" ], projection)
              :: List.map group.applications ~f:(fun application ->
                  let substitution =
                    List.fold application.source.declarations ~init:projection
                      ~f:(fun substitution declaration ->
                        match
                          Generic_proofs.matching_type declaration
                            group.representative.declarations
                        with
                        | Some target
                          when not (Ident.same declaration.typ_id target.typ_id) ->
                            Subst.add_type declaration.typ_id (Path.Pident target.typ_id)
                              substitution
                        | Some _ | None -> substitution)
                  in
                  ([ application.layout ], substitution))
            in
            let cell_environment =
              List.map layout_types ~f:(fun data ->
                  let aliases =
                    List.concat_map types ~f:(fun candidate ->
                        let same_namespace =
                          Option.exists candidate.Datatypes.cell_namespace
                            ~f:(fun owner ->
                              List.Assoc.mem field_contexts owner
                                ~equal:(List.equal String.equal))
                        in
                        let same_name =
                          Option.exists candidate.module_path ~f:(fun path ->
                              Option.equal String.equal (List.last path)
                                (Some data.Datatypes.module_name))
                        in
                        if same_namespace && same_name then
                          candidate.paths
                          @ Option.to_list
                              (Option.map candidate.id ~f:(fun id -> Path.Pident id))
                        else [])
                  in
                  Datatypes.with_paths data aliases)
              @ environment
            in
            let cell_fields =
              List.filter_map !refs ~f:(fun cell ->
                  let name = Qualified_name.of_string cell.cell_name in
                  Option.map
                    (List.Assoc.find field_contexts name.path
                       ~equal:(List.equal String.equal))
                    ~f:(fun substitution ->
                      (name.name, Subst.type_expr substitution cell.cell_type)))
              |> List.dedup_and_sort ~compare:(fun (left, _) (right, _) ->
                  String.compare left right)
            in
            let* cell_fields =
              all cell_fields ~f:(fun (field, elt) ->
                  let* typ =
                    Datatypes.typ cell_environment
                      ~at:group.representative.template.mod_loc elt
                  in
                  Ok (Datatypes.field_member cell_environment ~loc:l field typ elt))
            in
            let shape =
              R.Member.module_ ~loc:l ~interface:true (ident ~loc:l "Shape")
                (data_members @ fields @ cell_fields)
            in
            let factory =
              R.Member.unit_factory ~loc:l
                ~implements:[ (q (world ^ ".Shape"), []) ]
                (ident ~loc:l "Fresh") []
            in
            Ok
              (R.Member.module_ ~loc:l
                 ~params:
                   (List.map (Generic_modules.type_slots group) ~f:(fun stem ->
                        (ident ~loc:l stem, R.Name.make ~loc:l ~path:[ "Library" ] "Type")))
                 (ident ~loc:l world)
                 (List.nth_exn generic_interfaces
                    (List.findi_exn generics ~f:(fun _ candidate ->
                         phys_equal candidate group)
                    |> fst)
                 @ [ shape; factory; worker ])))
  in
  let* generic_instances =
    all generics ~f:(fun group ->
        all group.applications ~f:(fun application ->
            let views =
              List.map application.source.parameters ~f:(fun parameter ->
                  List.find_exn checked_modules ~f:(fun view ->
                      phys_equal view.Checked_modules.binding
                        parameter.Module_inventory.argument))
            in
            let view_names = List.map views ~f:(fun view -> view.Checked_modules.name) in
            let l = loc application.source.argument.site.item_loc in
            let q = qualified_name ~loc:l in
            let* setup, worker, arguments =
              match group.world with
              | None -> Ok ([], group.name, view_names)
              | Some world ->
                  let* arguments =
                    all application.source.parameters ~f:(fun parameter ->
                        let concrete =
                          checked_raw_types types parameter.Module_inventory.argument
                        in
                        all parameter.argument.expected.signature_types
                          ~f:(fun (_, declaration) ->
                            let t =
                              Btype.newgenty
                                (Tconstr
                                   ( Path.Pident declaration.Typedtree.typ_id,
                                     [],
                                     ref Types.Mnil ))
                            in
                            Datatypes.typ concrete ~at:declaration.typ_loc t)
                        |> Result.bind ~f:(fun ordinary ->
                            all parameter.argument.expected.signature_ghost_modules
                              ~f:(fun (_, formal) ->
                                let resource = formal.Module_inventory.ghost_resource in
                                Datatypes.typ concrete ~at:resource.resource_at
                                  resource.resource_type)
                            |> Result.map ~f:(fun carriers -> ordinary @ carriers)))
                    |> Result.map ~f:List.concat
                  in
                  let selected =
                    if List.is_empty (Generic_modules.type_slots group) then
                      R.Member.alias ~loc:l (ident ~loc:l application.world) (q world)
                    else
                      R.Member.instance ~loc:l
                        ~def:(q world, arguments)
                        (ident ~loc:l application.world)
                        (q world)
                  in
                  let canonical =
                    List.find_exn group.applications ~f:(fun other ->
                        Path.same other.source.identity application.source.identity)
                  in
                  let fresh =
                    if phys_equal canonical application then
                      [
                        R.Member.unit_instance ~loc:l
                          (ident ~loc:l canonical.layout)
                          (q (application.world ^ ".Fresh"));
                      ]
                    else []
                  in
                  Ok
                    ( selected :: fresh,
                      application.world ^ "." ^ (Qualified_name.of_string group.name).name,
                      view_names @ [ canonical.layout ] )
            in
            Ok
              ( application.source.argument,
                setup,
                R.Member.instance ~loc:l
                  ~def:
                    ( q worker,
                      List.map arguments ~f:(fun n -> R.Type.named ~loc:l (q n) []) )
                  (ident ~loc:l application.name)
                  (q worker) )))
  in
  let generic_instances = List.concat generic_instances in
  let _, native_blocks =
    List.fold (List.zip_exn checked_modules checked_module_members) ~init:([], [])
      ~f:(fun (emitted, blocks) (view, members) ->
        let binding = view.Checked_modules.binding in
        let captured =
          List.exists generics ~f:(fun group ->
              List.exists group.Generic_modules.captures ~f:(fun stage ->
                  List.exists stage.applications ~f:(fun application ->
                      phys_equal application.source.argument binding)))
        in
        let final =
          List.exists generics ~f:(fun group ->
              List.exists group.Generic_modules.applications ~f:(fun application ->
                  phys_equal application.source.argument binding))
        in
        if captured && not final then (emitted, blocks)
        else
          let attached =
            List.concat_map generics ~f:(fun group ->
                List.concat_map group.Generic_modules.applications ~f:(fun application ->
                    if not (phys_equal application.source.argument binding) then []
                    else
                      List.filter_map (List.drop_last_exn application.source.parameters)
                        ~f:(fun parameter ->
                          let argument = parameter.Module_inventory.argument in
                          Option.some_if
                            (not (List.mem emitted argument ~equal:phys_equal))
                            argument)))
          in
          let rec attach (emitted, attached) argument =
            if List.mem emitted argument ~equal:phys_equal then (emitted, attached)
            else
              let view =
                List.find_exn checked_modules ~f:(fun view ->
                    phys_equal view.Checked_modules.binding argument)
              in
              let dependency =
                Option.bind view.target ~f:(fun target ->
                    List.find checked_modules ~f:(fun candidate ->
                        String.equal candidate.Checked_modules.name target))
              in
              let emitted, attached =
                Option.value_map dependency ~default:(emitted, attached)
                  ~f:(fun dependency -> attach (emitted, attached) dependency.binding)
              in
              (argument :: emitted, argument :: attached)
          in
          let _, attached = List.fold attached ~init:(emitted, []) ~f:attach in
          let attached = List.rev attached in
          let attached_members =
            List.concat_map attached ~f:(fun argument ->
                snd
                  (List.find_exn (List.zip_exn checked_modules checked_module_members)
                     ~f:(fun (view, _) ->
                       phys_equal view.Checked_modules.binding argument)))
          in
          let prefix =
            List.concat_map
              (List.zip_exn generics
                 (List.zip_exn generic_interfaces generic_implementations))
              ~f:(fun (group, (interface, implementation)) ->
                if phys_equal group.representative.argument binding then
                  match group.Generic_modules.world with
                  | None -> interface @ [ implementation ]
                  | Some _ -> [ implementation ]
                else [])
          in
          let instances =
            List.filter_map generic_instances ~f:(fun (argument, _, instance) ->
                Option.some_if (phys_equal argument binding) instance)
          in
          let publications =
            List.filter_map !publication_members ~f:(fun (owner, member) ->
                Option.some_if
                  (phys_equal owner binding || List.mem attached owner ~equal:phys_equal)
                  (R.Member.callable member))
          in
          let setup =
            List.concat_map generic_instances ~f:(fun (argument, setup, _) ->
                if phys_equal argument binding then setup else [])
          in
          List.iter generics ~f:(fun group ->
              List.iter group.Generic_modules.applications ~f:(fun application ->
                  if
                    phys_equal application.source.argument binding
                    && Option.is_some group.world
                  then available_layouts := application.layout :: !available_layouts));
          let declarations = take_declarations () in
          List.iter generics ~f:(fun group ->
              List.iter group.Generic_modules.applications ~f:(fun application ->
                  if phys_equal application.source.argument binding then
                    available_layouts := application.name :: !available_layouts));
          let after_instances = take_declarations () in
          ( (binding :: attached) @ emitted,
            (prefix @ setup @ declarations @ publications @ attached_members @ members
           @ instances @ after_instances)
            :: blocks ))
  in
  let native_modules = List.concat (List.rev native_blocks) in

  let file_start = { Lexing.dummy_pos with pos_fname = source.file } in
  let start = R.Loc.make file_start file_start in
  let ref_fields =
    List.filter_map !refs ~f:(fun cell ->
        Option.some_if
          (List.is_empty (Qualified_name.of_string cell.cell_name).path)
          cell.cell_declaration)
  in
  let root_members =
    emit_context_members Module_context.Flat ~at:start ~representations:[]
      ~native_resources:deferred_native_resource_members ~applications:native_modules
      ~late_members:(List.concat_map !pending_declarations ~f:snd @ ref_fields)
  in
  Ok
    ( R.Program.make ~loc:start
        (Prelude.members
        @ (if
             shared.dynamic_indices
             || List.exists generic_shared ~f:(fun (_, shared) -> shared.dynamic_indices)
           then Indexed_initialization.members
           else [])
        @ imported_resource_members @ modules @ library_modules @ root_members),
      !origins )
