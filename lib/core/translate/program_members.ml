(** The fifth phase of a program's translation: library modules, the members of checked
    views, resources, types, ghost contracts, modules, predicates, lemmas and logical
    functions, and the translated pure functions and procedures. *)

open Base
open Translate_context
open Procedures
open Program_items
open Proof_declarations

type t = {
  library_modules : (Library_modules.t * R.Member.t list) list;
  library_worker_members : (string * R.Member.t list) list;
  publication_members : (Module_inventory.checked_binding * R.Callable.t) list;
      (** The pure functions that checked operations call, published as procedures, latest
          first. *)
  generic_interfaces : R.Member.t list list;
  checked_module_members : R.Member.t list list;
  action_check_lists : (structure * R.Member.t list) list;
  pending_member_lists : (structure * R.Member.t list) list;
  pred_members : R.Callable.t list;
  lemma_members : R.Callable.t list;
  logical_members : R.Member.t list;
  pure_funcs : (Procedures.func * R.Callable.t) list;
  procs : (Procedures.func * R.Callable.t) list;
}

let run (scopes : Program_scopes.t) (decls : Program_declarations.t)
    (proofs : Program_proofs.t) (shaped : Program_structures.t) state :
    (t * State.state, error) Result.t =
  let {
    Program_scopes.access_proofs;
    annotations;
    definition_member_name;
    definition_target;
    funcs;
    generics;
    initializations;
    inventory;
    libraries;
    linearizations;
    return_proofs;
    _;
  } =
    scopes
  in
  let declaration_context =
    Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
      ~unapplied_proofs:scopes.unapplied_proofs
  in
  let declaration_environment =
    Program_scopes.declaration_environment ~source:scopes.source
      ~unapplied_proofs:scopes.unapplied_proofs
  in
  let declaration_scope =
    Program_scopes.declaration_scope ~unapplied_proofs:scopes.unapplied_proofs
  in
  let proof_worker =
    Program_scopes.proof_worker ~module_contexts:scopes.module_contexts
      ~unapplied_proofs:scopes.unapplied_proofs
  in
  let scoped_binding =
    Program_scopes.scoped_binding ~unapplied_proofs:scopes.unapplied_proofs
  in
  let {
    Program_declarations.all_resource_views;
    all_resources;
    checked_modules;
    checked_operations;
    functions;
    layouts;
    library_preds;
    lifted;
    ocaml_env;
    predicates;
    procedure_signatures;
    pure;
    polymorphic_functions;
    generic_predicates;
    runtime_destinations;
    scoped_proofs;
    source;
    types;
    _;
  } =
    decls
  in
  let body_destination =
    Program_declarations.body_destination ~polymorphic_functions ~generics:scopes.generics
      ~module_contexts:scopes.module_contexts
      ~context_for_group:
        (Program_scopes.context_for_group ~module_contexts:scopes.module_contexts)
  in
  let body_module_context =
    Program_declarations.body_module_context ~module_contexts:scopes.module_contexts
      ~context_for_group:
        (Program_scopes.context_for_group ~module_contexts:scopes.module_contexts)
      ~generics:scopes.generics
  in
  let body_owner = Program_declarations.body_owner ~generics:scopes.generics in
  let body_proc_name =
    Program_declarations.body_proc_name ~polymorphic_functions ~generics:scopes.generics
      ~generic_procedures:decls.generic_procedures ~procedures:decls.procedures
  in
  let body_pure_name =
    Program_declarations.body_pure_name ~polymorphic_functions ~generics:scopes.generics
  in
  let body_pure_reference =
    Program_declarations.body_pure_reference ~polymorphic_functions
      ~generics:scopes.generics
  in
  let is_pure = Program_declarations.is_pure ~pure:decls.pure in
  let proc_name = Program_declarations.proc_name ~procedures:decls.procedures in
  let pure_name = Program_declarations.pure_name ~generics:scopes.generics in
  let resource_view =
    Program_declarations.resource_view ~untyped_scoped_proofs:scopes.scoped_proofs
  in
  let {
    Program_proofs.all_logical_functions;
    checked_resource_entries;
    checked_views;
    lemma_context;
    lemma_declarations;
    logical_declarations;
    preds;
    proof_support;
    spec_funcs;
    _;
  } =
    proofs
  in
  let context_owners = Program_proofs.context_owners ~source:decls.source in
  let module_context =
    Program_proofs.module_context
      ~scoped_binding:
        (Program_scopes.scoped_binding ~unapplied_proofs:scopes.unapplied_proofs)
      ~module_parameters:proofs.module_parameters
  in
  let proof_context = Program_proofs.proof_context proofs.proof_env in
  let proof_context_for =
    Program_proofs.proof_context_for proofs.proof_env
      ~declaration_context:
        (Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
           ~unapplied_proofs:scopes.unapplied_proofs)
      ~declaration_scope:
        (Program_scopes.declaration_scope ~unapplied_proofs:scopes.unapplied_proofs)
      ~scoped_binding:
        (Program_scopes.scoped_binding ~unapplied_proofs:scopes.unapplied_proofs)
      ~module_parameters:proofs.module_parameters
  in
  let {
    Program_structures.ghost_args;
    past_returns;
    past_structures;
    pasts;
    shared;
    structures;
    _;
  } =
    shaped
  in
  let body_shared =
    Program_structures.body_shared
      ~body_module_context:
        (Program_declarations.body_module_context ~module_contexts:scopes.module_contexts
           ~context_for_group:
             (Program_scopes.context_for_group ~module_contexts:scopes.module_contexts)
           ~generics:scopes.generics)
      ~shared:shaped.shared ~generic_shared:shaped.generic_shared
  in
  let owner_destination =
    Program_structures.owner_destination
      ~declaration_context:
        (Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
           ~unapplied_proofs:scopes.unapplied_proofs)
  in
  let shared_for_proof =
    Program_structures.shared_for_proof
      ~declaration_context:
        (Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
           ~unapplied_proofs:scopes.unapplied_proofs)
      ~shared:shaped.shared ~generic_shared:shaped.generic_shared
  in
  (* Each library's module, trusted: its abstract predicates, and its values, as functions
     without arguments, and functions, as procedures with their contracts. *)
  let library_polymorphic_functions =
    List.filter polymorphic_functions ~f:(fun worker ->
        not
          (List.exists funcs ~f:(fun f -> Ident.same worker.Polymorphic_functions.id f.id)))
  in
  let library_registry =
    Path_bindings.of_list
      (List.concat_map library_polymorphic_functions ~f:(fun worker ->
           List.map worker.paths ~f:(fun path -> (path, worker))))
  in
  let* library_emissions, state =
    State.run_from state
    @@ State.all libraries ~f:(fun (lib : Library_modules.t) ->
        let l = loc Location.none in
        let pred_members =
          all
            (List.filter library_preds ~f:(fun ((lib' : Library_modules.t), _, _) ->
                 String.equal lib'.library_name lib.library_name))
            ~f:(fun (_, (p : S.predicate), param_types) ->
              let worker =
                Generic_predicates.find generic_predicates
                  (lib.source_name ^ "." ^ p.pred_name.pid_str)
              in
              let types =
                Option.value_map worker ~default:types ~f:(fun worker ->
                    Generic_predicates.types worker types)
              in
              let* params =
                all (List.zip_exn p.pred_params param_types) ~f:(fun ((x, _), t) ->
                    let* typ = Datatypes.typ types ~at:x.S.pid_loc t in
                    Ok (t, R.Var.make ~loc:l (ident ~loc:l x.pid_str) typ))
              in
              let* implicit = implicit_parameters p in
              let explicit, implicit =
                List.split_n params (List.length params - implicit)
              in
              let kind = if p.pred_persistent then R.Callable.Inv else R.Callable.Pred in
              let member =
                R.Member.free
                  (R.Member.callable
                     (R.Callable.func ~loc:l ~kind ~formals:(List.map explicit ~f:snd)
                        ~returns:(List.map implicit ~f:snd)
                        (ident ~loc:l p.pred_name.pid_str)
                        None))
              in
              Ok (member, worker))
        in
        let open State.Syntax in
        let* environment = State.of_result (Library_modules.environment source lib) in
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
          scoped_contract_context types ~shared ~environment ~proof_support ~preds
            ~primitive_namespace:[ lib.library_name ] ~generic_predicates ~spec_funcs
            ~own_preds ~own_inputs ()
        in
        let ctx =
          {
            ctx with
            given =
              {
                ctx.given with
                generic_predicates;
                polymorphic_functions = library_registry;
              };
          }
        in
        let* pred_members = State.of_result pred_members in
        let* contracts = State.of_result (interface_contracts lib.library) in
        let+ value_members =
          State.in_procedure
          @@ State.all lib.library.signature ~f:(fun (item : Parsetree.signature_item) ->
              match item.psig_desc with
              | Psig_value vd ->
                  let at = vd.pval_loc in
                  let x = vd.pval_name.txt in
                  let value = Env.find_value (Pdot (lib.library_path, x)) source.env in
                  let worker =
                    Path_bindings.find library_registry (Pdot (lib.library_path, x))
                  in
                  let ctx =
                    match worker with
                    | None -> ctx
                    | Some worker ->
                        let types =
                          List.mapi worker.scheme.variables ~f:(fun index variable ->
                              Datatypes.variable_type ~variable
                                ~owner:(String.split worker.name ~on:'.')
                                ~parameter:("A" ^ Int.to_string index)
                                ~at:worker.loc)
                          @ types
                        in
                        {
                          ctx with
                          given =
                            {
                              ctx.given with
                              types;
                              primitive_namespace = String.split worker.name ~on:'.';
                            };
                        }
                  in
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
                  let+ member = library_function ctx ~at ~name:x ~args ~result contract in
                  let member = R.Member.free (R.Member.callable member) in
                  begin match worker with
                  | None -> ([ member ], [])
                  | Some worker -> ([], [ (worker.name, [ member ]) ])
                  end
              | Psig_type _ | Psig_attribute _ -> State.return ([], [])
              | _ ->
                  State.of_result
                    (unsupported item.psig_loc "This item of a library's interface"))
        in
        let ordinary_predicates =
          List.filter_map pred_members ~f:(function
            | member, None -> Some member
            | _, Some _ -> None)
        in
        let predicate_workers =
          List.filter_map pred_members ~f:(function
            | member, Some worker -> Some (worker.name, [ member ])
            | _, None -> None)
        in
        ( lib,
          ordinary_predicates @ List.concat_map value_members ~f:fst,
          predicate_workers @ List.concat_map value_members ~f:snd ))
  in
  let library_modules =
    List.map library_emissions ~f:(fun (library, members, _) -> (library, members))
  in
  let library_worker_members =
    List.concat_map library_emissions ~f:(fun (_, _, workers) -> workers)
  in
  (* The context of the requested [operation] of [view], with its arguments' and result's
     types. *)
  let view_operation_context ?(primitive_namespace = []) (view : checked_view) operation =
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
      Proof_types.realize_signature_ghost_environment source
        ~substitution:view.view_binding.parameter_substitution
        (List.map view.view_binding.expected.signature_ghost_modules
           ~f:(fun (_, formal) -> formal.Module_inventory.ghost_declaration))
        (Source.annotation_env source signature.site.environment)
    in
    let ctx =
      scoped_contract_context view.view_types ~shared ~environment
        ~proof_support:{ proof_support with strict_source_types = true }
        ~preds ~spec_funcs ~own_preds ~own_inputs:(List.filter_opt own_inputs)
        ~primitive_namespace ~generic_predicates ()
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
    Ok (ctx, args, result)
  in
  (* The contract of [operation] as [view] requests it, with its context and that
     context's own state. *)
  let prepare_view_operation ?(primitive_namespace = []) view operation =
    let open State.Syntax in
    let* ctx, args, result =
      State.of_result (view_operation_context ~primitive_namespace view operation)
    in
    let+ expected, local =
      State.within State.new_local
        (prepare_callable ~validate:true ctx
           ~at:operation.operation_signature.site.item_loc ~args ~result
           operation.operation_contract)
    in
    (ctx, local, args, result, expected)
  in
  (* The forwarding procedures of the checked operations, the pure functions they call
     published as procedures, and the contracts the operations' paths were prepared with. *)
  let* (adapter_members, publication_members), state =
    State.run_from state
    @@ State.map ~f:(fun (adapters, _, _, publication_members) ->
        (List.rev adapters, publication_members))
    @@ State.fold checked_operations ~init:([], [], [], [])
         ~f:(fun
             (adapters, checked_prepared, publications, publication_members) operation ->
           let open State.Syntax in
           let binding = operation.operation_binding in
           let view =
             List.find_exn checked_views ~f:(fun view ->
                 phys_equal view.view_binding binding)
           in
           let signature = operation.operation_signature in
           let at = binding.site.item_loc in
           let member = signature.declaration.val_name.txt in
           let actual_path = Path.Pdot (binding.actual_path, member) in
           let* ctx, local, args, result, expected =
             prepare_view_operation view operation
           in
           let* ( (actual, actual_contract, actual_projection, actual_at, actual_name),
                  publications,
                  publication_members ) =
             match List.Assoc.find checked_prepared actual_path ~equal:Path.same with
             | Some info -> State.return (info, publications, publication_members)
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
                     let* () =
                       State.of_result (check_adapter_shape ~at:f.loc f.contract)
                     in
                     let* () =
                       if
                         (is_pure f && logical_contract f.contract)
                         || (not (List.is_empty f.captured))
                         || Option.is_some f.role
                       then
                         State.of_result
                           (unsupported at
                              "A pure or lifted operation in a checked module binding")
                       else State.return ()
                     in
                     let actual_ctx =
                       spec_context types ~shared ~ocaml_env:f.environment ~proof_support
                         ~preds ~spec_funcs ()
                     in
                     let actual_args =
                       List.filter_map f.params ~f:(fun p ->
                           match p.Typedtree.fp_kind with
                           | Tparam_pat pat -> Some pat.pat_type
                           | _ -> None)
                     in
                     State.in_procedure
                     @@
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
                       then
                         State.of_result
                           (unsupported at
                              "A history contract in a checked module binding")
                       else State.return ()
                     in
                     let+ target, publications, publication_members =
                       if not (is_pure f) then
                         State.return (proc_name f, publications, publication_members)
                       else
                         match List.Assoc.find publications f.id ~equal:Ident.same with
                         | Some publication ->
                             State.return (publication, publications, publication_members)
                         | None ->
                             let publication =
                               Fresh_names.fresh ("published_" ^ f.raven_name)
                             in
                             let+ body =
                               forwarding_body ~at ~self:publication ~target:(proc_name f)
                                 ~result:f.body.exp_type ~atomic:false prepared
                             in
                             ( publication,
                               (f.id, publication) :: publications,
                               ( binding,
                                 prepared_member ~at ~name:publication (Some body)
                                   prepared )
                               :: publication_members )
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
                     ( (prepared, f.contract, projection, f.loc, target),
                       publications,
                       publication_members )
                 | None ->
                     let library =
                       List.find libraries ~f:(fun lib ->
                           Path.same lib.Library_modules.library_path binding.actual_path)
                     in
                     begin match library with
                     | None ->
                         State.of_result
                           (unsupported at
                              "A checked module argument without a supported operation \
                               contract")
                     | Some lib ->
                         let* contracts =
                           State.of_result (interface_contracts lib.library)
                         in
                         let contract =
                           Option.map
                             (List.Assoc.find contracts member ~equal:String.equal)
                             ~f:fst
                         in
                         let* () = State.of_result (check_adapter_shape ~at contract) in
                         let value =
                           Env.find_value actual_path binding.site.environment
                         in
                         let actual_args, actual_result =
                           Signature_contract.arguments value.val_type
                         in
                         let own_preds =
                           List.filter_map library_preds ~f:(fun (library, p, ts) ->
                               Option.some_if
                                 (Path.same library.Library_modules.library_path
                                    lib.library_path)
                                 ( p.S.pred_name.pid_str,
                                   (library.library_name ^ "." ^ p.pred_name.pid_str, ts)
                                 ))
                         in
                         let own_inputs =
                           List.filter_map own_preds ~f:(fun (local, (target, _)) ->
                               Option.map
                                 (List.Assoc.find proof_support.predicate_inputs target
                                    ~equal:String.equal) ~f:(fun count -> (local, count)))
                         in
                         let* environment =
                           State.of_result (Library_modules.environment source lib)
                         in
                         let actual_ctx =
                           scoped_contract_context types ~shared ~environment
                             ~primitive_namespace:[ lib.library_name ] ~generic_predicates
                             ~proof_support ~preds ~spec_funcs ~own_preds ~own_inputs ()
                         in
                         let+ prepared =
                           State.in_procedure
                             (prepare_callable actual_ctx ~at:value.val_loc
                                ~args:actual_args ~result:actual_result contract)
                         in
                         ( ( prepared,
                             contract,
                             Subst.identity,
                             value.val_loc,
                             lib.library_name ^ "." ^ member ),
                           publications,
                           publication_members )
                     end)
           in
           let* () =
             State.of_result
             @@
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
             State.of_result
             @@
             if
               List.length expected_implicit = List.length actual_implicit
               && Poly.equal expected.prepared_roles actual.prepared_roles
             then Ok ()
             else
               unsupported at
                 "Different implicit argument shapes in a checked module binding"
           in
           let* () =
             State.of_result
             @@
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
             State.of_result
             @@
             if
               List.exists
                 (args @ [ result ]
                 @ List.map expected_implicit ~f:(fun (_, _, t, _, _) -> t))
                 ~f:(contains_atomic_token view.view_types)
             then unsupported at "Public atomic-update tokens in a checked module binding"
             else Ok ()
           in
           let* body, _ =
             State.within local
               (forwarding_body ~at ~self:operation.operation_name ~target:actual_name
                  ~result
                  ~atomic:(logical_contract operation.operation_contract)
                  expected)
           in
           let related =
             [
               (signature.site.item_loc, "The requested module operation");
               (actual_at, "The actual module operation");
             ]
           in
           let* () =
             State.iter
               [
                 ( R.Diagnostic.Precondition,
                   "The module argument's precondition is not provided by this view" );
                 ( Postcondition,
                   "The module argument does not establish this view's postcondition" );
                 ( Commit,
                   "The module argument does not establish this view's atomic \
                    postcondition" );
                 ( Abortable_call,
                   "This view's atomic update may not be restorable if the actual \
                    operation aborts" );
               ]
               ~f:(fun (code, message) ->
                 State.record_origin { at; code; message; related })
           in
           let+ () =
             State.record_origin
               {
                 at = { at with loc_start = at.loc_end };
                 code = Postcondition;
                 message =
                   "The module argument does not establish this view's postcondition";
                 related;
               }
           in
           let checked_prepared =
             List.fold operation.operation_paths ~init:checked_prepared
               ~f:(fun checked_prepared path ->
                 let projection =
                   match path with
                   | Path.Pdot (parent, _) -> checked_type_substitution binding parent
                   | _ -> view.view_source_substitution
                 in
                 ( path,
                   ( expected,
                     operation.operation_contract,
                     projection,
                     signature.site.item_loc,
                     operation.operation_name ) )
                 :: checked_prepared)
           in
           (* Grouped adapters inherit their instantiated interface contracts. *)
           let inherit_contract =
             List.exists checked_modules ~f:(fun checked ->
                 phys_equal checked.Checked_modules.binding binding
                 && checked.grouped && Option.is_none checked.target)
           in
           let member =
             if inherit_contract then
               R.Callable.proc ~loc:(loc at) ~formals:expected.prepared_formals
                 ~returns:expected.prepared_returns
                 (ident ~loc:(loc at) operation.operation_member)
                 (Some body)
             else
               prepared_member ~at ~name:operation.operation_member (Some body) expected
           in
           ( (operation, expected, member) :: adapters,
             checked_prepared,
             publications,
             publication_members ))
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
        let* implicit = implicit_parameters p in
        let formals, returns = List.split_n vars (List.length vars - implicit) in
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
            let stem =
              List.Assoc.find_exn group.Generic_modules.types source ~equal:String.equal
            in
            match declaration.Typedtree.typ_manifest with
            | None ->
                let interface = qualified_name ~loc:l Prelude.value_interface in
                if aliases then
                  let source_type = Ctype.newconstr (Path.Pident declaration.typ_id) [] in
                  begin match Datatypes.dictionary_name view.view_types source_type with
                  | Some dictionary ->
                      Ok
                        (Some
                           (R.Member.alias ~loc:l (ident ~loc:l stem)
                              (qualified_name ~loc:l dictionary)))
                  | None ->
                      unsupported at "A canonical source-value dictionary for this type"
                  end
                else
                  Ok
                    (Some
                       (match group.Generic_modules.world with
                       | None -> R.Member.instance ~loc:l (ident ~loc:l stem) interface
                       | Some world ->
                           R.Member.alias ~loc:l (ident ~loc:l stem)
                             (qualified_name ~loc:l (world ^ "." ^ stem))))
            | Some manifest ->
                let* definition =
                  match group.Generic_modules.world with
                  | Some world ->
                      Ok
                        (R.Type.named ~loc:l (R.Name.make ~loc:l ~path:[ world ] stem) [])
                  | None -> Datatypes.typ view.view_types ~at manifest.ctyp_type
                in
                Ok (Some (R.Member.type_ ~loc:l (ident ~loc:l stem) (Some definition))))
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
  let* generic_interfaces, state =
    State.run_from state
    @@ State.all generics ~f:(fun owner ->
        State.all (Generic_modules.parameter_groups owner) ~f:(fun group ->
            let open State.Syntax in
            let view = symbolic_view group (String.split group.interface ~on:'.') in
            let* types = State.of_result (type_members group view ~aliases:false) in
            let* resources =
              State.of_result (resource_members group view ~aliases:false)
            in
            let* ghost_modules =
              State.of_result
                (ghost_module_members ~aliases:false group.representative.argument)
            in
            let* operations =
              State.all checked_operations ~f:(fun operation ->
                  if
                    not
                      (phys_equal operation.operation_binding
                         group.representative.argument)
                  then State.return None
                  else
                    let+ _, _, _, _, prepared =
                      prepare_view_operation
                        ~primitive_namespace:(String.split group.interface ~on:'.')
                        view operation
                    in
                    Some
                      (R.Member.callable
                         (prepared_member ~at:operation.operation_signature.site.item_loc
                            ~name:operation.operation_member None prepared)))
            in
            let* requests, dictionaries, instances =
              State.gets (fun (state : State.state) ->
                  ( state.tables.domains,
                    state.tables.dictionaries,
                    state.tables.function_instances ))
            in
            let* domains =
              State.of_result
                (Result.all
                   (List.map requests ~f:(fun request ->
                        Datatypes.domain_members request.domain_types
                          [ request.domain_type ])
                   @ List.map dictionaries ~f:(fun request ->
                       Datatypes.domain_members ~dictionaries:true request.domain_types
                         [ request.domain_type ])))
            in
            let namespace = String.split group.interface ~on:'.' in
            let domains =
              List.concat domains |> Datatypes.unique_domain_members
              |> List.filter_map ~f:(fun (qualified, member) ->
                  Option.some_if
                    (List.equal String.equal (Qualified_name.of_string qualified).path
                       namespace)
                    member)
            in
            let l = loc group.representative.argument.site.item_loc in
            let instances =
              List.filter_map instances ~f:(fun instance ->
                  Option.some_if
                    (List.equal String.equal instance.instance_namespace namespace)
                    (Value_instances.member ~loc:l instance))
            in
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
            State.return
              (carriers
              @ [
                  R.Member.module_ ~loc:l ~interface:true
                    (ident ~loc:l (Qualified_name.of_string group.interface).name)
                    (types @ domains @ resources @ ghost_modules @ instances
                   @ List.filter_opt operations);
                ])))
  in
  let generic_interfaces = List.map generic_interfaces ~f:List.concat in
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
  let* action_check_lists, state =
    State.run_from state
    @@ State.all structures ~f:(fun st ->
        let preds, spec_funcs, proof_support =
          proof_context_for ~preds ~spec_funcs ~proof_support st.invariant
        in
        let ctx =
          spec_context types
            ~shared:(shared_for_proof st.invariant)
            ~ocaml_env:st.environment ~preds ~spec_funcs ~proof_support
            ~primitive_namespace:(declaration_context st.invariant).namespace
            ~generic_predicates ()
        in
        State.map
          (State.in_procedure (action_checks ctx st))
          ~f:(fun members -> (st, members)))
  in
  let* pending_member_lists, state =
    State.run_from state
    @@ State.all structures ~f:(fun st ->
        let members =
          State.all st.pendings ~f:(fun p ->
              match List.find funcs ~f:(fun f -> Ident.same f.id p.helped) with
              | Some helped ->
                  let preds, spec_funcs, proof_support =
                    proof_context_for ~preds ~spec_funcs ~proof_support st.invariant
                  in
                  State.in_procedure
                    (pending_members
                       (spec_context types
                          ~shared:(shared_for_proof st.invariant)
                          ~ocaml_env:st.environment ~preds ~spec_funcs ~proof_support
                          ~primitive_namespace:
                            (declaration_context st.invariant).namespace
                          ~generic_predicates ())
                       st p helped
                       ~helped_proc:
                         (match owner_destination st.invariant with
                         | Module_context.Flat -> proc_name helped
                         | Module_context.Worker _ | Module_context.Function_worker _
                         | Module_context.Generic_predicate _ ->
                             body_proc_name helped))
              | None ->
                  State.of_result
                    (error st.at
                       (Printf.sprintf "There is no function %s to help"
                          (Ident.name p.helped))))
        in
        State.map members ~f:(fun members -> (st, List.concat members)))
  in
  let* pred_members, state =
    State.run_from state
    @@ State.all predicates ~f:(fun (at, p, def, param_types) ->
        let preds, spec_funcs, proof_support =
          proof_context_for ~preds ~spec_funcs ~proof_support p.pred_name.pid_str
        in
        let worker = Generic_predicates.find generic_predicates p.pred_name.pid_str in
        let types =
          Option.value_map worker ~default:types ~f:(fun worker ->
              Generic_predicates.types worker types)
        in
        let declaration_name =
          match worker with
          | Some worker -> Some (Generic_predicates.member worker)
          | None -> definition_member_name p.pred_name.pid_str
        in
        let primitive_namespace =
          Option.value_map worker
            ~default:(declaration_context p.pred_name.pid_str).namespace ~f:(fun worker ->
              String.split worker.name ~on:'.')
        in
        predicate types
          ~shared:(shared_for_proof p.pred_name.pid_str)
          ~ocaml_env:(declaration_environment p.pred_name.pid_str)
          ~preds ~spec_funcs ~proof_support ?declaration_name ~generic_predicates
          ~primitive_namespace ~at ~structures p def param_types)
  in
  let predicate_bodies =
    List.filter_map predicates ~f:(fun (_, p, definition, _) ->
        match definition with
        | (Body body | Direct_invariant body)
          when Option.is_none (scoped_binding p.pred_name.pid_str) ->
            Some
              ( p.S.pred_name.pid_str,
                {
                  definition = body;
                  inline = p.pred_inline;
                  environment = ocaml_env;
                  project_type = Fn.id;
                } )
        | Body _ | Direct_invariant _ -> None
        | Invariant _ | View _ -> None)
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        match binding.kind with
        | Predicate (predicate, Plain body)
          when binding.exported && not (Proof_bindings.opaque scoped_proofs binding) ->
            Some
              ( binding.public_key,
                {
                  definition = body;
                  inline = predicate.pred_inline;
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
          | Predicate (predicate, Plain body)
            when Proof_bindings.visible scoped_proofs ~scope binding
                 && not (Proof_bindings.opaque_at scoped_proofs ~scope binding) ->
              Some
                ( binding.public_key,
                  {
                    definition = body;
                    inline = predicate.pred_inline;
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
          | Predicate (predicate, Plain body)
            when Proof_bindings.application_visible ~owners scoped_proofs ~scope view
                 && not
                      (Proof_bindings.application_opaque ~owners scoped_proofs ~scope view)
            ->
              Some
                ( view.key,
                  {
                    definition = body;
                    inline = predicate.pred_inline;
                    environment = view.source.environment;
                    project_type = (fun ty -> project (view.project_type ty));
                  } )
          | _ -> None)
      @ predicate_bodies
    in
    List.filter_map (Proof_bindings.private_bindings scoped_proofs ~scope)
      ~f:(fun binding ->
        match binding.kind with
        | Predicate (predicate, Plain body) ->
            Some
              ( binding.backend,
                {
                  definition = body;
                  inline = predicate.pred_inline;
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
  let* lemma_members, state =
    State.run_from state
    @@ State.all lemma_declarations ~f:(fun declaration ->
        let declaration_name = (Proof_scopes.name declaration).pid_str in
        let scope = declaration_scope declaration_name in
        let preds, spec_funcs, proof_support =
          proof_context_for ~preds ~spec_funcs ~proof_support declaration_name
        in
        let lemmas = lemma_context scope in
        let lemmas =
          module_lemmas (declaration_context declaration_name) ~project:Fn.id lemmas
        in
        proof_lemma types ~shared
          ~primitive_namespace:(declaration_context declaration_name).namespace
          ~generic_predicates
          ~ocaml_env:(declaration_environment declaration_name)
          ~preds ~spec_funcs ~proof_lemmas:lemmas ~proof_support
          ~predicate_bodies:(body_contexts scope)
          ?member_name:(definition_member_name declaration_name)
          declaration)
  in
  let* logical_members, state =
    State.run_from state
    @@ State.all
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
                      (Option.equal String.equal (definition_target binding)
                         (Some backend))
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
             List.mem previous
               (implementation_key signature.lemma_raven)
               ~equal:String.equal
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
           State.bind
             (State.of_result
             @@
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
             | _ -> Ok ())
             ~f:(fun () ->
               proof_function types ~shared
                 ~primitive_namespace:(declaration_context declaration_name).namespace
                 ~generic_predicates
                 ~ocaml_env:(declaration_environment declaration_name)
                 ~preds ~spec_funcs
                 ~proof_support:{ proof_support with logical_functions }
                 ?member_name:(definition_member_name declaration_name)
                 ~as_value:
                   (match declaration with
                   | S.Proof_function { function_params = []; _ } -> true
                   | _ -> false)
                 declaration))
  in
  let pure_functions =
    Path_bindings.of_list
      (List.concat_map pure ~f:(fun f ->
           List.map f.paths ~f:(fun path -> (path, pure_name f))))
  in
  let* runtime_contexts =
    all runtime_destinations ~f:(fun destination ->
        let groups = Module_context.groups destination in
        let namespace =
          Module_context.namespace
            (match destination with
            | Module_context.Function_worker (_, parent)
            | Module_context.Generic_predicate (_, parent) ->
                parent
            | Flat | Worker _ -> destination)
        in
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
        let body_types =
          match destination with
          | Module_context.Function_worker (worker, _) ->
              let f = List.find_exn funcs ~f:(fun f -> Ident.same worker.id f.id) in
              Program_declarations.function_types polymorphic_functions f body_types
          | Module_context.Generic_predicate (worker, _) ->
              Generic_predicates.types worker body_types
          | Flat | Worker _ -> body_types
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
              (Option.is_some f.lexical_owner
              && Option.is_some
                   (Program_declarations.enclosing_worker polymorphic_functions f)
              &&
              match body_owner f with
              | Some (_, false) -> false
              | Some (_, true) | None -> true)
              || List.exists groups ~f:(fun group ->
                  match body_owner f with
                  | Some (owner, true) -> phys_equal group owner
                  | Some (_, false) | None -> false))
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
  let polymorphic_registry destination =
    let current_groups = Module_context.groups destination in
    Path_bindings.of_list
      (library_registry.entries
      @ List.concat_map funcs ~f:(fun candidate ->
          let worker =
            match Generic_modules.member generics candidate.id with
            | None -> Program_declarations.function_worker polymorphic_functions candidate
            | Some (group, application, stem) ->
                let source =
                  List.find_map group.body_members ~f:(fun (source, target) ->
                      Option.some_if (String.equal stem target) source)
                in
                let representative =
                  Option.bind source ~f:(fun source ->
                      List.Assoc.find group.representative.body_members source
                        ~equal:String.equal)
                in
                Option.bind representative ~f:(fun id ->
                    List.find polymorphic_functions ~f:(fun worker ->
                        Ident.same worker.Polymorphic_functions.id id))
                |> Option.map ~f:(fun (worker : Polymorphic_functions.t) ->
                    if List.exists current_groups ~f:(phys_equal group) then worker
                    else
                      {
                        worker with
                        name =
                          application.name ^ "."
                          ^ (Qualified_name.of_string worker.name).name;
                      })
          in
          Option.value_map worker ~default:[] ~f:(fun worker ->
              List.map candidate.paths ~f:(fun path -> (path, worker)))))
  in
  let polymorphic_registries =
    if List.is_empty polymorphic_functions then []
    else
      List.map runtime_destinations ~f:(fun destination ->
          (destination, polymorphic_registry destination))
  in
  let body_polymorphic_registry f =
    Option.value
      (List.Assoc.find polymorphic_registries (body_destination f)
         ~equal:Module_context.same_destination)
      ~default:Path_bindings.empty
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
  let body_primitive_namespace f = Module_context.namespace (body_destination f) in
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
  let* pure_funcs, state =
    State.run_from state
    @@ State.all pure ~f:(fun f ->
        let open State.Syntax in
        match body_owner f with
        | Some (_, false) -> State.return None
        | _ ->
            let* environment = State.of_result (body_environment f) in
            let f = { f with environment } in
            let data, predicates, _, pure_functions, spec_funcs, proof_support =
              body_context f
            in
            let declaration_name =
              Module_context.local_name (body_destination f) (body_pure_name f)
            in
            let primitive_namespace = body_primitive_namespace f in
            let+ member =
              func data ~shared:(body_shared f) ~ocaml_env:f.environment ~preds:predicates
                ~funcs:pure_functions ~spec_funcs ~proof_support ~declaration_name
                ~primitive_namespace ~polymorphic_functions:(body_polymorphic_registry f)
                ~lifted ~generic_predicates
                ?current_polymorphic:
                  (Program_declarations.enclosing_worker polymorphic_functions f)
                f
            in
            Some (f, member))
  in
  let* procs, state =
    State.run_from state
    @@ State.all funcs ~f:(fun f ->
        let open State.Syntax in
        match body_owner f with
        | Some (_, false) -> State.return None
        | _ ->
            let* environment = State.of_result (body_environment f) in
            let f = { f with environment } in
            let data, predicates, functions, _, spec_funcs, proof_support =
              body_context f
            in
            let declaration_name =
              Module_context.local_name (body_destination f) (body_proc_name f)
            in
            let primitive_namespace = body_primitive_namespace f in
            let+ member =
              let given =
                {
                  (declaration_inputs data ~shared:(body_shared f) ~env:f.environment
                     ~preds:predicates ~spec_funcs ~proof_support ~primitive_namespace
                     ~polymorphic_functions:(body_polymorphic_registry f)
                     ~generic_predicates
                     ?current_polymorphic:
                       (Program_declarations.enclosing_worker polymorphic_functions f)
                     ())
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
              proc ~given
                ~past_structures:(past_structures ~symbolic:true f)
                ~proc_name:(body_proc_name f) ~pure:(is_pure f) ~declaration_name
                ~pure_name:(body_pure_reference f) f
            in
            Some (f, member))
  in
  let pure_funcs = List.filter_opt pure_funcs and procs = List.filter_opt procs in
  Ok
    ( {
        library_modules;
        library_worker_members;
        publication_members;
        generic_interfaces;
        checked_module_members;
        action_check_lists;
        pending_member_lists;
        pred_members;
        lemma_members;
        logical_members;
        pure_funcs;
        procs;
      },
      state )
