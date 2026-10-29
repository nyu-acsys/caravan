(** The fifth phase of a program's translation: library modules, the members of checked
    views, resources, types, ghost contracts, modules, predicates, lemmas and logical
    functions, and the translated pure functions and procedures. *)

open Base
open Translate_context
open Procedures
open Program_items
open Proof_declarations

type t = {
  library_modules : R.Member.t list;
  publication_members : (Module_inventory.checked_binding * R.Callable.t) list Base.ref;
  generic_interfaces : R.Member.t list list;
  checked_module_members : R.Member.t list list;
  action_check_lists : (structure * R.Member.t list) list;
  pending_member_lists : (structure * R.Member.t list) list;
  pred_members : R.Callable.t list;
  lemma_members : R.Callable.t list;
  logical_members : R.Member.t list;
  runtime_primitives :
    (Module_context.destination * (string * R.Member.t) list Base.ref) list;
  pure_funcs : (Procedures.func * R.Callable.t) list;
  procs : (Procedures.func * R.Callable.t) list;
}

let run (scopes : Program_scopes.t) (decls : Program_declarations.t)
    (proofs : Program_proofs.t) (shaped : Program_structures.t) : (t, error) Result.t =
  let {
    Program_scopes.access_proofs;
    annotations;
    definition_member_name;
    definition_target;
    fresh;
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
    origins;
    predicates;
    primitives;
    procedure_signatures;
    pure;
    refs;
    runtime_destinations;
    scoped_proofs;
    source;
    types;
    _;
  } =
    decls
  in
  let body_destination =
    Program_declarations.body_destination ~generics:scopes.generics
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
    Program_declarations.body_proc_name ~generics:scopes.generics
      ~generic_procedures:decls.generic_procedures ~procedures:decls.procedures
  in
  let body_pure_name = Program_declarations.body_pure_name ~generics:scopes.generics in
  let body_pure_reference =
    Program_declarations.body_pure_reference ~generics:scopes.generics
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
  let proof_context =
    Program_proofs.proof_context ~definition_target:scopes.definition_target
      ~source:decls.source ~proof_assets:decls.proof_assets ~types:decls.types
      ~scoped_proofs:decls.scoped_proofs ~scoped_inputs:decls.scoped_inputs
      ~private_scoped_inputs:proofs.private_scoped_inputs
      ~all_logical_functions:proofs.all_logical_functions
      ~au_application_view:
        (Program_declarations.au_application_view
           ~untyped_scoped_proofs:scopes.scoped_proofs)
  in
  let proof_context_for =
    Program_proofs.proof_context_for
      ~declaration_context:
        (Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
           ~unapplied_proofs:scopes.unapplied_proofs)
      ~declaration_scope:
        (Program_scopes.declaration_scope ~unapplied_proofs:scopes.unapplied_proofs)
      ~definition_target:scopes.definition_target ~source:decls.source
      ~proof_assets:decls.proof_assets ~types:decls.types
      ~scoped_proofs:decls.scoped_proofs ~scoped_inputs:decls.scoped_inputs
      ~private_scoped_inputs:proofs.private_scoped_inputs
      ~all_logical_functions:proofs.all_logical_functions
      ~au_application_view:
        (Program_declarations.au_application_view
           ~untyped_scoped_proofs:scopes.scoped_proofs)
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
  Ok
    {
      library_modules;
      publication_members;
      generic_interfaces;
      checked_module_members;
      action_check_lists;
      pending_member_lists;
      pred_members;
      lemma_members;
      logical_members;
      runtime_primitives;
      pure_funcs;
      procs;
    }
