(** The third phase of a program's translation: checked views, predicate inputs, logical
    functions, proof support and contexts, atomic updates, and lemmas. *)

open Base
open Translate_context
open Procedures
open Program_items
open Proof_declarations

(** What the proof contexts of declarations and procedures are computed from. *)
module Proof_env = struct
  type t = {
    definition_target : Proof_bindings.binding -> string option;
    source : Source.t;
    proof_assets :
      Proof_scopes.scope option -> Source.proof_resource list * Source.proof_field list;
    types : Datatypes.t list;
    scoped_proofs : Proof_bindings.t;
    scoped_inputs : (string * int) list;
    private_scoped_inputs : (string * int) list;
    all_logical_functions : (string * lemma_signature) list;
    au_application_view : Source.proof_au -> Proof_bindings.application option;
  }
end

type t = {
  checked_views : Program_items.checked_view list;
  checked_resource_entries :
    (Path.t * string * Program_items.resource_signature * Types.type_expr list) list;
  logical_declarations : S.proof_decl list;
  all_logical_functions : (string * lemma_signature) list;
  generic_callables : Generic_parameters.t list;
  proof_support : proof_support;
  preds : (string * (string * Types.type_expr list)) list;
  spec_funcs : (string * string) list;
  lemma_declarations : Source.S.proof_decl list;
  lemma_context :
    ?at:Location.t -> Proof_scopes.scope option -> (string * lemma_signature) list;
  module_parameters :
    (Module_context.t
    * ((string * Ident.t list) * string * Types.type_expr list * int) list)
    list;
  private_scoped_inputs : (string * int) list;
  proof_env : Proof_env.t;
}

let atomic_predicates_of signatures =
  List.concat_map signatures ~f:(fun signature ->
      List.map [ "pending"; "committed" ] ~f:(fun method_ ->
          let inputs, _ = Option.value_exn (atomic_inputs signature method_) in
          let key = signature.au_key ^ "." ^ method_ in
          (key, (key, inputs))))

let context_atomic ~(source : Source.t) ~(scoped_proofs : Proof_bindings.t)
    ~(au_application_view : Source.proof_au -> Proof_bindings.application option)
    ?current_procedure scope signatures =
  let environment =
    Option.value_map scope ~default:source.env ~f:(fun scope ->
        Source.annotation_env source scope.Proof_scopes.environment)
  in
  let public = Proof_bindings.public_type scoped_proofs in
  let rebase = Proof_bindings.context_type scoped_proofs ~environment in
  let inside owner =
    match (owner, scope) with
    | None, _ -> true
    | Some owner, Some caller ->
        Option.exists (Proof_scopes.find_owner source.proof_scopes (Some owner))
          ~f:(fun parent ->
            Option.is_some
              (Proof_bindings.drop_prefix parent.namespace caller.Proof_scopes.namespace))
    | Some _, None -> false
  in
  List.filter_map signatures ~f:(fun signature ->
      let au = signature.au_source in
      let binding =
        List.find scoped_proofs.bindings ~f:(fun binding ->
            match binding.kind with
            | Atomic actual -> Ident.same actual.au_id au.au_id
            | _ -> false)
      in
      if
        match au.au_application with
        | None ->
            Option.exists binding ~f:(fun binding ->
                not (Proof_bindings.visible scoped_proofs ~scope binding))
        | Some _ ->
            not
              (Option.exists (au_application_view au)
                 ~f:(Proof_bindings.application_visible scoped_proofs ~scope))
      then None
      else
        let private_operation =
          Option.equal String.equal current_procedure (Some signature.au_procedure)
          || inside signature.au_owner
        in
        let project = if private_operation then Fn.id else fun ty -> rebase (public ty) in
        let token =
          if inside au.au_scope then au.au_token else rebase (public au.au_token)
        in
        let signature =
          map_atomic_types
            {
              signature with
              au_inputs = signature.au_private.inputs;
              au_result = signature.au_private.result;
              au_ghost_outputs = signature.au_private.ghost_outputs;
              au_implicit = signature.au_private.implicit;
            }
            ~f:project
        in
        let token =
          match Types.get_desc token with
          | Tconstr (path, _, _) -> Ctype.newconstr path signature.au_source.au_parameters
          | _ -> token
        in
        Some { signature with au_token = token })

let context_owners ~(source : Source.t) at =
  Option.value_map at ~default:[] ~f:(Proof_scopes.owners_at source.proof_scopes)

let proof_context (proof_env : Proof_env.t) ?current_procedure ?at scope preds spec_funcs
    proof_support =
  let {
    Proof_env.definition_target;
    source;
    proof_assets;
    types;
    scoped_proofs;
    scoped_inputs;
    private_scoped_inputs;
    all_logical_functions;
    au_application_view;
  } =
    proof_env
  in
  let context_atomic = context_atomic ~source ~scoped_proofs ~au_application_view in
  let context_owners = context_owners ~source in
  let owners = context_owners at in
  let atomic_updates =
    context_atomic ?current_procedure scope proof_support.atomic_updates
  in
  let atomic_keys = List.map (atomic_predicates_of proof_support.atomic_updates) ~f:fst in
  let atomic_preds = atomic_predicates_of atomic_updates in
  let preds =
    List.filter preds ~f:(fun (key, _) ->
        not (List.mem atomic_keys key ~equal:String.equal))
    @ atomic_preds
  in
  let spec_funcs =
    List.filter spec_funcs ~f:(fun (key, _) ->
        not (List.mem atomic_keys key ~equal:String.equal))
    @ List.map atomic_preds ~f:(fun (key, _) -> (key, key))
  in
  let proof_support = { proof_support with atomic_updates } in
  let resources, ghost_fields = proof_assets scope in
  let proof_support = { proof_support with resources; ghost_fields } in
  let environment =
    Option.value_map scope ~default:source.env ~f:(fun scope ->
        Source.annotation_env source scope.Proof_scopes.environment)
  in
  let project = Proof_bindings.context_type scoped_proofs ~environment in
  let local_exports = Proof_bindings.local_exports scoped_proofs ~scope in
  let preds =
    List.filter_map local_exports ~f:(fun binding ->
        match binding.kind with
        | Predicate _ -> Some (binding.public_key, (binding.backend, binding.public_types))
        | Lemma _ | Function _ | Resource _ | Field _ | Atomic _ | State _ | Action _ ->
            None)
    @ preds
  in
  let predicate_inputs =
    List.filter_map local_exports ~f:(fun binding ->
        Option.map (List.Assoc.find scoped_inputs binding.backend ~equal:String.equal)
          ~f:(fun count -> (binding.public_key, count)))
    @ proof_support.predicate_inputs
  in
  let logical_functions =
    List.filter_map local_exports ~f:(fun binding ->
        match binding.kind with
        | Function (S.Proof_function declaration) ->
            let inputs, outputs =
              List.split_n binding.public_types (List.length declaration.function_params)
            in
            let signature =
              List.Assoc.find_exn all_logical_functions binding.backend
                ~equal:String.equal
            in
            Some
              ( binding.public_key,
                { signature with lemma_inputs = inputs; lemma_outputs = outputs } )
        | _ -> None)
    @ proof_support.logical_functions
  in
  let opaque_predicates =
    List.filter proof_support.opaque_predicates ~f:(fun key ->
        not
          (List.exists scoped_proofs.bindings ~f:(fun binding ->
               String.equal binding.public_key key
               && not (Proof_bindings.opaque_at scoped_proofs ~scope binding))))
    @ List.filter_map local_exports ~f:(fun binding ->
        Option.some_if
          (Proof_bindings.opaque_at scoped_proofs ~scope binding)
          binding.public_key)
  in
  let proof_support =
    { proof_support with predicate_inputs; logical_functions; opaque_predicates }
  in
  let spec_funcs =
    List.map logical_functions ~f:(fun (key, signature) -> (key, signature.lemma_raven))
    @ List.map preds ~f:(fun (key, (backend, _)) -> (key, backend))
    @ spec_funcs
  in
  let preds =
    List.map preds ~f:(fun (key, (backend, types)) ->
        (key, (backend, Compiler_types.map_group types ~f:project)))
  in
  let logical_functions =
    List.map proof_support.logical_functions ~f:(fun (key, signature) ->
        ( key,
          {
            signature with
            lemma_inputs = List.map signature.lemma_inputs ~f:project;
            lemma_outputs = List.map signature.lemma_outputs ~f:project;
          } ))
  in
  let proof_support = { proof_support with logical_functions } in
  let application_views =
    List.filter scoped_proofs.applications
      ~f:(Proof_bindings.application_visible ~owners scoped_proofs ~scope)
  in
  let application_preds =
    List.filter_map application_views ~f:(fun view ->
        match view.source.kind with
        | Predicate _ ->
            Some (view.key, (view.backend, Compiler_types.map_group view.types ~f:project))
        | _ -> None)
  in
  let application_inputs =
    List.filter_map application_views ~f:(fun view ->
        Option.map (List.Assoc.find scoped_inputs view.source.backend ~equal:String.equal)
          ~f:(fun count -> (view.key, count)))
  in
  let application_functions =
    List.filter_map application_views ~f:(fun view ->
        match view.source.kind with
        | Function _ ->
            Option.map
              (List.Assoc.find all_logical_functions view.source.backend
                 ~equal:String.equal) ~f:(fun signature ->
                let inputs, outputs =
                  List.split_n view.types (List.length signature.lemma_inputs)
                in
                ( view.key,
                  {
                    signature with
                    lemma_raven = view.backend;
                    lemma_inputs = List.map inputs ~f:project;
                    lemma_outputs = List.map outputs ~f:project;
                  } ))
        | _ -> None)
  in
  let proof_support =
    {
      proof_support with
      logical_functions = application_functions @ proof_support.logical_functions;
    }
  in
  let spec_funcs =
    List.map application_functions ~f:(fun (key, signature) ->
        (key, signature.lemma_raven))
    @ spec_funcs
  in
  let preds = application_preds @ preds in
  let spec_funcs =
    List.map application_preds ~f:(fun (key, (backend, _)) -> (key, backend)) @ spec_funcs
  in
  let proof_support =
    {
      proof_support with
      predicate_inputs = application_inputs @ proof_support.predicate_inputs;
      opaque_predicates =
        List.filter_map application_views ~f:(fun view ->
            Option.some_if
              (Proof_bindings.application_opaque ~owners scoped_proofs ~scope view)
              view.key)
        @ proof_support.opaque_predicates;
    }
  in
  let bindings = Proof_bindings.private_bindings scoped_proofs ~scope in
  let private_preds =
    List.filter_map bindings ~f:(fun binding ->
        match binding.kind with
        | Predicate _ ->
            Some
              ( binding.backend,
                ( Option.value (definition_target binding) ~default:binding.backend,
                  binding.private_types ) )
        | Lemma _ | Function _ | Resource _ | Field _ | Atomic _ | State _ | Action _ ->
            None)
  in
  let inputs =
    List.filter_map bindings ~f:(fun binding ->
        Option.map
          (List.Assoc.find private_scoped_inputs binding.backend ~equal:String.equal)
          ~f:(fun count -> (binding.backend, count)))
  in
  let private_functions =
    List.filter_map bindings ~f:(fun binding ->
        Option.map
          (List.Assoc.find all_logical_functions binding.backend ~equal:String.equal)
          ~f:(fun signature ->
            ( binding.backend,
              {
                signature with
                lemma_raven =
                  Option.value (definition_target binding) ~default:signature.lemma_raven;
              } )))
  in
  ( private_preds @ preds,
    List.filter_map bindings ~f:(fun binding ->
        match binding.kind with
        | Function _ ->
            Some
              ( binding.entry.name.pid_str,
                Option.value (definition_target binding) ~default:binding.backend )
        | Predicate _ | Lemma _ | Resource _ | Field _ | Atomic _ | State _ | Action _ ->
            None)
    @ List.map private_functions ~f:(fun (key, signature) -> (key, signature.lemma_raven))
    @ List.map private_preds ~f:(fun (key, (backend, _)) -> (key, backend))
    @ spec_funcs,
    {
      proof_support with
      proof_key =
        (fun environment q ->
          Proof_bindings.resolve ~owners scoped_proofs ~scope ~environment q);
      predicate_inputs = inputs @ proof_support.predicate_inputs;
      logical_functions = private_functions @ proof_support.logical_functions;
    } )

let module_context ~(scoped_binding : string -> Proof_bindings.binding option)
    ~(module_parameters :
       (Module_context.t
       * ((string * Ident.t list) * string * Types.type_expr list * int) list)
       list) context ~projection (preds, spec_funcs, support) =
  let project =
    if List.is_empty context.Module_context.parameters then Fn.id
    else Subst.type_expr projection
  in
  let target backend =
    match scoped_binding backend with
    | Some binding when Module_context.contains context binding ->
        Module_context.member context backend
    | _ -> backend
  in
  let parameters = List.Assoc.find_exn module_parameters context ~equal:phys_equal in
  let preds =
    List.map preds ~f:(fun (key, (backend, ts)) ->
        (key, (target backend, Compiler_types.map_group ts ~f:project)))
  in
  let preds =
    List.map parameters ~f:(fun (_, key, ts, _) ->
        (key, (key, Compiler_types.map_group ts ~f:project)))
    @ preds
  in
  let spec_funcs =
    List.map parameters ~f:(fun (_, key, _, _) -> (key, key))
    @ List.map spec_funcs ~f:(fun (key, backend) -> (key, target backend))
  in
  let predicate_views =
    List.fold parameters ~init:support.predicate_views
      ~f:(fun views ((name, parameters), key, _, _) ->
        List.fold parameters ~init:views ~f:(fun views parameter ->
            Path_bindings.add views (Path.Pdot (Path.Pident parameter, name)) key))
  in
  ( preds,
    spec_funcs,
    {
      support with
      predicate_views;
      resources =
        List.map support.resources ~f:(fun resource ->
            let resource = Source.map_resource_types resource ~f:project in
            {
              resource with
              resource_path = Subst.module_path projection resource.resource_path;
            });
      ghost_fields =
        List.map support.ghost_fields ~f:(fun field ->
            let field = Source.map_field_types field ~f:project in
            {
              field with
              field_resource =
                Option.map field.field_resource ~f:(Subst.module_path projection);
            });
      atomic_updates =
        List.map support.atomic_updates ~f:(fun signature ->
            map_atomic_types signature ~f:project);
      logical_functions =
        List.map support.logical_functions ~f:(fun (key, signature) ->
            let inputs, outputs =
              List.split_n
                (Compiler_types.map_group
                   (signature.lemma_inputs @ signature.lemma_outputs)
                   ~f:project)
                (List.length signature.lemma_inputs)
            in
            ( key,
              {
                signature with
                lemma_raven = target signature.lemma_raven;
                lemma_inputs = inputs;
                lemma_outputs = outputs;
              } ));
      predicate_inputs =
        List.map parameters ~f:(fun (_, key, _, inputs) -> (key, inputs))
        @ support.predicate_inputs;
      opaque_predicates =
        List.map parameters ~f:(fun (_, key, _, _) -> key) @ support.opaque_predicates;
    } )

let proof_context_for (proof_env : Proof_env.t)
    ~(declaration_context : string -> Module_context.t)
    ~(declaration_scope : string -> Proof_scopes.scope option)
    ~(scoped_binding : string -> Proof_bindings.binding option)
    ~(module_parameters :
       (Module_context.t
       * ((string * Ident.t list) * string * Types.type_expr list * int) list)
       list) ~preds ~spec_funcs ~proof_support name =
  let proof_context = proof_context proof_env in
  let module_context = module_context ~scoped_binding ~module_parameters in
  let context = declaration_context name in
  module_context context ~projection:Subst.identity
    (proof_context (declaration_scope name) preds spec_funcs proof_support)

let run ?(family_plan = Generic_family_plan.empty) (scopes : Program_scopes.t)
    (decls : Program_declarations.t) state : (t * State.state, error) Result.t =
  let {
    Program_scopes.definition_target;
    funcs;
    generics;
    inventory;
    libraries;
    module_contexts;
    public_types;
    _;
  } =
    scopes
  in
  let alias_path = Program_scopes.alias_path in
  let asset_context =
    Program_scopes.asset_context ~module_contexts:scopes.module_contexts
  in
  let declaration_environment =
    Program_scopes.declaration_environment ~source:scopes.source
      ~unapplied_proofs:scopes.unapplied_proofs
  in
  let scoped_binding =
    Program_scopes.scoped_binding ~unapplied_proofs:scopes.unapplied_proofs
  in
  let {
    Program_declarations.atomic_operations;
    generic_models;
    library_preds;
    predicates;
    procedure_signatures;
    proof_assets;
    pure;
    resource_types;
    scoped_inputs;
    scoped_proofs;
    source;
    token_types;
    types;
    _;
  } =
    decls
  in
  let generic_callable ~key ~at ~explicit parameters =
    let context =
      Program_scopes.declaration_context ~module_contexts:scopes.module_contexts
        ~unapplied_proofs:scopes.unapplied_proofs key
    in
    let name =
      String.concat ~sep:"."
        (context.namespace
        @ [ Fresh_names.fresh ("PolyProof$" ^ (Qualified_name.of_string key).name) ])
    in
    let* worker =
      Generic_parameters.discover ~expand:(Datatypes.expand types) ~key ~name ~at
        ~explicit parameters
    in
    let worker =
      { worker with name = Generic_family_plan.proof family_plan key worker.name }
    in
    if List.is_empty worker.variables then Ok None else Ok (Some worker)
  in
  let au_application_view =
    Program_declarations.au_application_view ~untyped_scoped_proofs:scopes.scoped_proofs
  in
  let au_plan =
    Program_declarations.au_plan
      ~asset_context:
        (Program_scopes.asset_context ~module_contexts:scopes.module_contexts)
  in
  let au_procedure =
    Program_declarations.au_procedure ~polymorphic_functions:decls.polymorphic_functions
      ~procedures:decls.procedures ~generics:scopes.generics
      ~generic_procedures:decls.generic_procedures
      ~asset_context:
        (Program_scopes.asset_context ~module_contexts:scopes.module_contexts)
  in
  let proc_name = Program_declarations.proc_name ~procedures:decls.procedures in
  let pure_name = Program_declarations.pure_name ~generics:scopes.generics in
  let pure_reference = Program_declarations.pure_reference ~generics:scopes.generics in
  let resource_signatures =
    List.map library_preds ~f:(fun (lib, p, ts) ->
        {
          resource_paths =
            [ Path.Pdot (lib.Library_modules.library_path, p.S.pred_name.pid_str) ];
          resource_declaration = p;
          resource_backend = lib.library_name ^ "." ^ p.pred_name.pid_str;
          resource_types = ts;
          resource_raw_types = ts;
        })
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        match (binding.Proof_bindings.kind, binding.entry.scope.owner) with
        | Predicate (p, _), Some owner when binding.exported ->
            let declaration =
              Proof_bindings.constraints_for scoped_proofs binding
              |> List.filter ~f:(fun constraint_ ->
                  constraint_.Module_inventory.restricts_visibility)
              |> List.rev
              |> List.find_map ~f:(fun constraint_ ->
                  List.Assoc.find
                    constraint_.Module_inventory.signature.signature_resources
                    binding.entry.name.pid_str ~equal:String.equal)
              |> Option.value_map ~default:p ~f:(fun formal ->
                  formal.Module_inventory.declaration)
            in
            let original = Path.Pdot (owner, binding.entry.name.pid_str) in
            let paths =
              List.fold inventory.aliases ~init:[ original ]
                ~f:(fun paths (alias, target) ->
                  paths @ List.filter_map paths ~f:(alias_path ~alias ~target))
            in
            Some
              {
                resource_paths = paths;
                resource_declaration = declaration;
                resource_backend = binding.backend;
                resource_types = binding.public_types;
                resource_raw_types = binding.public_types;
              }
        | _ -> None)
  in
  let resource_signatures =
    resource_signatures
    @ List.filter_map scoped_proofs.applications ~f:(fun view ->
        match view.Proof_bindings.source.kind with
        | Predicate (p, _)
          when Proof_bindings.application_visible scoped_proofs ~scope:None view ->
            Some
              {
                resource_paths = [ Path.Pdot (view.path, view.source.entry.name.pid_str) ];
                resource_declaration = p;
                resource_backend = view.backend;
                resource_types = view.types;
                resource_raw_types = view.types;
              }
        | _ -> None)
  in
  let* checked_views, _ =
    List.fold_result inventory.bindings ~init:([], resource_signatures)
      ~f:(fun (views, resources) binding ->
        let source_path = List.hd_exn binding.Module_inventory.paths in
        let source_substitution = checked_type_substitution binding source_path in
        let actual_substitution =
          checked_type_substitution ~substitution:binding.parameter_substitution binding
            binding.actual_path
        in
        let view_types = checked_raw_types types binding in
        let* view_resources =
          all binding.expected.signature_resources ~f:(fun (member, formal) ->
              let wanted = Path.Pdot (binding.actual_path, member) in
              match
                List.find resources ~f:(fun resource ->
                    List.mem resource.resource_paths wanted ~equal:Path.same)
              with
              | None ->
                  error binding.site.item_loc
                    ("The actual module does not declare resource " ^ member)
              | Some actual ->
                  let declaration = formal.Module_inventory.declaration in
                  let* () =
                    if Option.is_none declaration.pred_body then Ok ()
                    else
                      unsupported formal.site.item_loc
                        "A resource definition in a checked module signature"
                  in
                  let* () =
                    if
                      Bool.equal declaration.pred_persistent
                        actual.resource_declaration.pred_persistent
                      && List.length declaration.pred_params
                         = List.length actual.resource_types
                    then Ok ()
                    else
                      error binding.site.item_loc
                        ("The resource declaration " ^ member
                       ^ " has a different kind or arity")
                  in
                  let environment =
                    Source.annotation_env source formal.site.environment
                  in
                  let* raw =
                    Proof_bindings.parameter_types environment declaration.pred_params
                  in
                  let projected =
                    Compiler_types.map_group raw ~f:(Subst.type_expr actual_substitution)
                  in
                  let implemented =
                    Compiler_types.map_group actual.resource_types
                      ~f:(Subst.type_expr binding.parameter_substitution)
                  in
                  let* equal =
                    Signature_contract.compiler ~at:binding.site.item_loc (fun () ->
                        Ctype.is_equal binding.site.environment true projected implemented)
                  in
                  let* () =
                    if equal then Ok ()
                    else
                      error binding.site.item_loc
                        ("The resource declaration " ^ member
                       ^ " has different parameter types")
                  in
                  let* expected = implicit_parameters declaration in
                  let* actual_implicit =
                    implicit_parameters actual.resource_declaration
                  in
                  let* () =
                    if expected = actual_implicit then Ok ()
                    else
                      error binding.site.item_loc
                        ("The resource declaration " ^ member
                       ^ " has different implicit parameters")
                  in
                  Ok
                    ( formal,
                      {
                        resource_paths =
                          List.map binding.paths ~f:(fun path -> Path.Pdot (path, member));
                        resource_declaration = declaration;
                        resource_backend = actual.resource_backend;
                        resource_types =
                          Compiler_types.map_group raw
                            ~f:(Subst.type_expr source_substitution);
                        resource_raw_types = raw;
                      } ))
        in
        let view =
          {
            view_binding = binding;
            view_key =
              Fresh_names.fresh
                ("view$" ^ String.uncapitalize (String.concat ~sep:"_" binding.namespace));
            view_resources;
            view_source_substitution = source_substitution;
            view_actual_substitution = actual_substitution;
            view_types;
          }
        in
        let aliases =
          List.concat_map view_resources ~f:(fun (_, resource) ->
              List.map resource.resource_paths ~f:(fun path ->
                  match path with
                  | Path.Pdot (parent, _) ->
                      {
                        resource with
                        resource_paths = [ path ];
                        resource_types =
                          List.map resource.resource_raw_types
                            ~f:
                              (Subst.type_expr (checked_type_substitution binding parent));
                      }
                  | _ -> resource))
        in
        Ok (views @ [ view ], resources @ aliases))
  in
  let checked_resource_entries =
    List.concat_map checked_views ~f:(fun view ->
        List.concat_map view.view_resources ~f:(fun (_, resource) ->
            List.mapi resource.resource_paths ~f:(fun index path ->
                let ts =
                  match path with
                  | Path.Pdot (parent, _) ->
                      List.map resource.resource_raw_types
                        ~f:
                          (Subst.type_expr
                             (checked_type_substitution view.view_binding parent))
                  | _ -> resource.resource_types
                in
                let key =
                  view.view_key ^ "_" ^ Int.to_string index ^ "."
                  ^ resource.resource_declaration.pred_name.pid_str
                in
                (path, key, resource, ts))))
  in
  let checked_preds =
    List.map checked_resource_entries ~f:(fun (_, key, resource, ts) ->
        (key, (resource.resource_backend, ts)))
  in
  let* predicate_inputs =
    all
      (List.map predicates ~f:(fun (_, p, _, ts) -> (p.S.pred_name.pid_str, p, ts))
      @ List.map library_preds ~f:(fun ((lib : Library_modules.t), p, ts) ->
          (lib.source_name ^ "." ^ p.S.pred_name.pid_str, p, ts)))
      ~f:(fun (key, p, ts) ->
        let* count = implicit_parameter_count ~kind:"predicate" p.pred_params in
        Ok (Option.map count ~f:(fun count -> (key, List.length ts - count))))
  in
  let predicate_inputs = List.filter_opt predicate_inputs in
  let predicate_inputs =
    predicate_inputs
    @ List.filter_map library_preds ~f:(fun (lib, p, _) ->
        Option.map
          (List.Assoc.find predicate_inputs
             (lib.Library_modules.source_name ^ "." ^ p.S.pred_name.pid_str)
             ~equal:String.equal)
          ~f:(fun count -> (lib.library_name ^ "." ^ p.pred_name.pid_str, count)))
  in
  let* checked_inputs =
    all checked_resource_entries ~f:(fun (_, key, resource, ts) ->
        let* count =
          implicit_parameter_count ~kind:"predicate"
            resource.resource_declaration.pred_params
        in
        Ok
          (Option.map
             (Option.first_some
                (Option.map count ~f:(fun count -> List.length ts - count))
                (List.Assoc.find scoped_inputs resource.resource_backend
                   ~equal:String.equal))
             ~f:(fun count -> (key, count))))
  in
  let predicate_inputs = List.filter_opt checked_inputs @ predicate_inputs in
  let preds =
    List.map predicates ~f:(fun (_, p, _, types) ->
        (p.pred_name.pid_str, (p.pred_name.pid_str, types)))
    @ List.map library_preds ~f:(fun ((lib : Library_modules.t), p, types) ->
        let key = lib.source_name ^ "." ^ p.pred_name.pid_str in
        (key, (lib.library_name ^ "." ^ p.pred_name.pid_str, types)))
  in
  let preds =
    preds
    @ List.filter_map preds ~f:(fun (_, (target, types)) ->
        if List.Assoc.mem preds target ~equal:String.equal then None
        else Some (target, (target, types)))
  in
  let preds = checked_preds @ preds in
  let scoped_keys = List.map scoped_proofs.bindings ~f:(fun binding -> binding.backend) in
  let private_scoped_inputs = scoped_inputs in
  let predicate_inputs =
    List.filter predicate_inputs ~f:(fun (key, _) ->
        not (List.mem scoped_keys key ~equal:String.equal))
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        if binding.exported then
          Option.map
            (List.Assoc.find private_scoped_inputs binding.backend ~equal:String.equal)
            ~f:(fun count -> (binding.public_key, count))
        else None)
  in
  let preds =
    List.filter preds ~f:(fun (key, _) ->
        not (List.mem scoped_keys key ~equal:String.equal))
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        match binding.kind with
        | Predicate _ when binding.exported ->
            Some (binding.public_key, (binding.backend, binding.public_types))
        | _ -> None)
  in
  let logical_declarations =
    List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
        match entry.Proof_scopes.declaration with
        | S.Proof_function _ as declaration ->
            if Option.is_none entry.scope.owner then Some declaration
            else
              Option.bind
                (List.find scoped_proofs.bindings ~f:(fun binding ->
                     Ident.same binding.entry.id entry.id))
                ~f:scoped_function
        | _ -> None)
  in
  let* all_logical_functions =
    all logical_declarations ~f:(function
      | S.Proof_function { function_name; function_params; function_result; _ } ->
          let ocaml_env = declaration_environment function_name.pid_str in
          let* parameters =
            Source.ocaml_types ocaml_env ~at:function_name.pid_loc
              (List.map function_params ~f:snd @ [ function_result ])
          in
          let lemma_inputs, outputs =
            List.split_n parameters (List.length function_params)
          in
          let output = List.hd_exn outputs in
          let* lemma_generic =
            generic_callable ~key:function_name.pid_str ~at:function_name.pid_loc
              ~explicit:(List.length function_params) parameters
          in
          Ok
            ( function_name.pid_str,
              {
                lemma_raven = function_name.pid_str;
                lemma_constant = List.is_empty function_params;
                lemma_generic;
                lemma_inputs;
                lemma_implicit_count = 0;
                lemma_outputs = [ output ];
              } )
      | _ -> error Location.none "Expected a logical function declaration")
  in
  let logical_functions =
    List.filter all_logical_functions ~f:(fun (key, _) ->
        Option.is_none (scoped_binding key))
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        match binding.kind with
        | Function (S.Proof_function declaration) when binding.exported ->
            let inputs, outputs =
              List.split_n binding.public_types (List.length declaration.function_params)
            in
            let signature =
              List.Assoc.find_exn all_logical_functions binding.backend
                ~equal:String.equal
            in
            Some
              ( binding.public_key,
                { signature with lemma_inputs = inputs; lemma_outputs = outputs } )
        | _ -> None)
  in
  let resources, ghost_fields = proof_assets None in
  let proof_support =
    {
      runtime_functions =
        Path_bindings.of_list
          (List.concat_map pure ~f:(fun f ->
               List.filter_map f.paths ~f:(fun path ->
                   match path with
                   | Path.Pdot _ when not (List.is_empty f.signature_sites) -> None
                   | _ -> Some (path, pure_reference f))));
      predicate_views =
        Path_bindings.of_list
          (List.map checked_resource_entries ~f:(fun (path, key, _, _) -> (path, key)));
      public_types;
      strict_source_types = false;
      library_paths = library_paths libraries;
      atomic_updates = [];
      resources;
      ghost_fields;
      canonical_path = Proof_bindings.canonical_owner scoped_proofs;
      logical_functions;
      mathematical_types =
        generic_models @ source.proof_types @ source.logical_types @ resource_types
        @ token_types;
      predicate_inputs;
      proof_key =
        (fun environment q ->
          Proof_bindings.resolve scoped_proofs ~scope:None ~environment q);
      action_key =
        (fun id ->
          Proof_bindings.action_key scoped_proofs
            ~scope:(Proof_bindings.scope_for_location scoped_proofs id.S.pid_loc)
            id);
      opaque_predicates =
        Proof_bindings.opaque_keys scoped_proofs
        @ List.map checked_resource_entries ~f:(fun (_, key, _, _) -> key)
        @ List.concat_map library_preds ~f:(fun (library, p, _) ->
            [
              library.Library_modules.source_name ^ "." ^ p.pred_name.pid_str;
              library.library_name ^ "." ^ p.pred_name.pid_str;
            ]);
    }
  in
  let spec_funcs =
    List.map pure ~f:(fun f ->
        (String.concat ~sep:"." (f.namespace @ [ Ident.name f.id ]), pure_name f))
    @ List.map preds ~f:(fun (p, (raven, _)) -> (p, raven))
    @ List.map logical_functions ~f:(fun (n, s) -> (n, s.lemma_raven))
  in
  let context_atomic = context_atomic ~source ~scoped_proofs ~au_application_view in
  let context_owners = context_owners ~source in
  let proof_env =
    {
      Proof_env.definition_target;
      source;
      proof_assets;
      types;
      scoped_proofs;
      scoped_inputs;
      private_scoped_inputs;
      all_logical_functions;
      au_application_view;
    }
  in
  let proof_context = proof_context proof_env in
  let* module_parameters =
    all module_contexts.contexts ~f:(fun context ->
        let* resources =
          all context.Module_context.parameters ~f:(fun parameter ->
              let generic = parameter.Generic_proofs.generic in
              let signature = parameter.instance.argument.expected in
              let original =
                Option.value parameter.original ~default:parameter.instance.parameter
              in
              let substitution =
                List.fold signature.signature_types ~init:Subst.identity
                  ~f:(fun substitution (name, declaration) ->
                    Subst.add_type declaration.Typedtree.typ_id
                      (Path.Pdot (Path.Pident original, name))
                      substitution)
              in
              let substitution =
                List.fold signature.signature_ghost_modules ~init:substitution
                  ~f:(fun substitution (name, formal) ->
                    let resource = formal.Module_inventory.ghost_resource in
                    let owner = Path.Pdot (Path.Pident original, name) in
                    let substitution =
                      Subst.add_module resource.resource_id owner substitution
                    in
                    List.fold resource.resource_type_members ~init:substitution
                      ~f:(fun substitution (member, id, _) ->
                        Subst.add_type id
                          (Path.Pdot (owner, String.uncapitalize member))
                          substitution))
              in
              let* resources =
                all signature.signature_resources ~f:(fun (name, formal) ->
                    let environment =
                      Source.annotation_env source
                        formal.Module_inventory.site.environment
                    in
                    let* ts =
                      Proof_bindings.parameter_types environment
                        formal.declaration.pred_params
                    in
                    let ts =
                      Compiler_types.map_group ts ~f:(Subst.type_expr substitution)
                    in
                    let* implicit = implicit_parameters formal.declaration in
                    let stem =
                      List.Assoc.find_exn generic.resources name ~equal:String.equal
                    in
                    let key =
                      Module_context.member context (generic.parameter ^ "." ^ stem)
                    in
                    Ok
                      ( (name, [ original; parameter.instance.parameter ]),
                        key,
                        ts,
                        List.length ts - implicit ))
              in
              Ok resources)
        in
        Ok (context, List.concat resources))
  in
  let module_context = module_context ~scoped_binding ~module_parameters in
  let* atomic_updates, state =
    State.run_from state
    @@ State.all atomic_operations ~f:(fun (au_source, f) ->
        let open State.Syntax in
        let* scheme =
          State.of_result
            (Polymorphic_functions.discover ~expand:(Datatypes.expand types) ~at:f.loc
               f.scheme_type)
        in
        let preds, spec_funcs, proof_support =
          proof_context ~current_procedure:(proc_name f) ~at:f.loc
            (Proof_bindings.scope_for_location scoped_proofs f.loc)
            preds spec_funcs proof_support
        in
        let preds, spec_funcs, proof_support =
          let context =
            Program_declarations.body_module_context
              ~module_contexts:scopes.module_contexts
              ~context_for_group:
                (Program_scopes.context_for_group ~module_contexts:scopes.module_contexts)
              ~generics f
          in
          module_context context
            ~projection:
              (Program_declarations.source_function_projection ~generics context f)
            (preds, spec_funcs, proof_support)
        in
        let signature =
          List.Assoc.find_exn procedure_signatures (proc_name f) ~equal:String.equal
        in
        let groups =
          Option.value_map (au_plan au_source) ~default:[] ~f:(fun plan ->
              [ plan.Generic_proofs.group ])
        in
        let worker =
          Program_declarations.applied_function_worker ~generics
            ~polymorphic_functions:decls.polymorphic_functions ~groups ~canonical:Fn.id f
          |> Option.map ~f:(fun worker ->
              { worker with Polymorphic_functions.id = f.id; paths = f.paths; scheme })
        in
        let types = Program_declarations.function_types (Option.to_list worker) f types in
        let primitive_namespace =
          match worker with
          | Some worker -> String.split worker.name ~on:'.'
          | None ->
              Module_context.namespace (asset_context au_source.au_scope).destination
        in
        let ctx =
          spec_context types ~shared:no_shared ~ocaml_env:f.environment ~preds ~spec_funcs
            ~proof_support ~generic_predicates:decls.generic_predicates
            ~primitive_namespace ()
        in
        let ctx =
          {
            ctx with
            given =
              {
                ctx.given with
                current_polymorphic = worker;
                current_procedure = Some (au_procedure au_source f);
              };
          }
        in
        State.in_procedure
        @@ State.bind
             (State.bind (formals ctx f) ~f:(fun formals ->
                  contract_env ctx ~spec_funcs f formals ~result:"result"))
             ~f:(fun (_, _, implicit, _) ->
               let au_inputs =
                 List.filter_map f.params ~f:(fun p ->
                     match p.fp_kind with
                     | Tparam_pat pat -> Some pat.pat_type
                     | _ -> None)
                 @ List.map signature.procedure_inputs ~f:snd
               in
               let project =
                 match au_plan au_source with
                 | Some plan -> Subst.type_expr (Generic_proofs.source_projection plan)
                 | None ->
                     begin match Generic_modules.member generics f.id with
                     | Some (_, application, _) ->
                         let path =
                           match au_source.au_operation_path with
                           | Path.Pdot (owner, _) -> owner
                           | _ -> application.source.identity
                         in
                         Subst.type_expr
                           (Generic_proofs.implementation_projection application.source
                              path)
                     | None -> Fn.id
                     end
               in
               let shape =
                 {
                   inputs = au_inputs;
                   result = f.body.exp_type;
                   ghost_outputs = List.map signature.procedure_outputs ~f:snd;
                   implicit = List.map implicit ~f:(fun (_, _, ty, _) -> ty);
                 }
               in
               let key =
                 Option.first_some
                   (Option.map (au_application_view au_source) ~f:(fun view -> view.key))
                   (List.find_map scoped_proofs.bindings ~f:(fun binding ->
                        match binding.kind with
                        | Atomic actual when Ident.same actual.au_id au_source.au_id ->
                            Some binding.backend
                        | _ -> None))
                 |> Option.value ~default:au_source.au_name
               in
               let owner =
                 match au_plan au_source with
                 | Some plan -> plan.scope.owner
                 | None ->
                     begin match
                       Proof_bindings.scope_for_location scoped_proofs f.loc
                     with
                     | Some scope when List.equal String.equal scope.namespace f.namespace
                       ->
                         scope.owner
                     | _ ->
                         List.find_map f.paths ~f:(function
                           | Path.Pdot (owner, _) ->
                               Some (Proof_bindings.canonical_owner scoped_proofs owner)
                           | _ -> None)
                     end
               in
               let au_generic =
                 Option.map worker ~f:(fun worker ->
                     Generic_parameters.
                       {
                         key;
                         member =
                           (Qualified_name.of_string (au_procedure au_source f)).name;
                         name = worker.name;
                         loc = au_source.au_at;
                         parameters = [ worker.scheme.typ ];
                         variables = worker.scheme.variables;
                         explicit = 0;
                       })
               in
               let signature =
                 map_atomic_types
                   {
                     au_key = key;
                     au_generic;
                     au_owner = owner;
                     au_private = shape;
                     au_token = au_source.au_token;
                     au_source;
                     au_procedure = au_procedure au_source f;
                     au_inputs = shape.inputs;
                     au_result = shape.result;
                     au_returns_value = not (is_unit f.body.exp_type);
                     au_ghost_outputs = shape.ghost_outputs;
                     au_implicit = shape.implicit;
                   }
                   ~f:project
               in
               let open State.Syntax in
               let* signature =
                 match signature.au_generic with
                 | None -> State.return signature
                 | Some generic ->
                     let declaration = List.hd_exn generic.parameters in
                     let* arguments =
                       State.of_result
                         (Polymorphic_functions.instantiate
                            ~expand:(Datatypes.expand types) ~at:au_source.au_at
                            { typ = declaration; variables = generic.variables }
                            ~declaration ~occurrence:signature.au_source.au_operation_type)
                     in
                     State.return
                       (map_atomic_types signature ~f:(fun typ ->
                            Option.value_exn
                              (Datatypes.instantiate_alias generic.variables arguments typ)))
               in
               State.return
                 {
                   signature with
                   au_generic =
                     Option.map signature.au_generic ~f:(fun generic ->
                         {
                           generic with
                           parameters =
                             signature.au_token
                             :: (signature.au_inputs @ [ signature.au_result ]
                               @ signature.au_ghost_outputs @ signature.au_implicit);
                         });
                 }))
  in
  let proof_support = { proof_support with atomic_updates } in
  let atomic_predicates = atomic_predicates_of (context_atomic None atomic_updates) in
  let preds = preds @ atomic_predicates in
  let spec_funcs =
    spec_funcs @ List.map atomic_predicates ~f:(fun (key, _) -> (key, key))
  in
  let lemma_declarations =
    List.filter source.proof ~f:(function S.Proof_lemma _ -> true | _ -> false)
    @ List.filter_map scoped_proofs.bindings ~f:scoped_lemma
  in
  let* () =
    check_lemma_recursion lemma_declarations ~resolve:(fun at q ->
        let binding =
          List.find scoped_proofs.bindings ~f:(fun binding ->
              Poly.equal binding.entry.name.pid_loc at)
        in
        let scope = Option.map binding ~f:(fun binding -> binding.entry.scope) in
        let environment =
          Option.value_map binding ~default:source.env ~f:(fun binding ->
              binding.environment)
        in
        let key =
          Option.value
            (Proof_bindings.resolve scoped_proofs ~scope ~environment q)
            ~default:(qualid_key q)
        in
        Option.value (Proof_bindings.canonical_key scoped_proofs key) ~default:key)
  in
  let* all_proof_lemmas =
    all lemma_declarations ~f:(function
      | S.Proof_lemma { lemma_name; lemma_params; lemma_returns; _ } ->
          let ocaml_env = declaration_environment lemma_name.pid_str in
          let* implicit = implicit_parameter_count ~kind:"lemma" lemma_params in
          let lemma_implicit_count = Option.value implicit ~default:0 in
          let* parameters =
            Source.ocaml_types ocaml_env ~at:lemma_name.pid_loc
              (List.map (lemma_params @ lemma_returns) ~f:snd)
          in
          let lemma_inputs, lemma_outputs =
            List.split_n parameters (List.length lemma_params)
          in
          let* lemma_generic =
            generic_callable ~key:lemma_name.pid_str ~at:lemma_name.pid_loc
              ~explicit:(List.length lemma_inputs - lemma_implicit_count)
              parameters
          in
          if
            List.Assoc.mem spec_funcs lemma_name.pid_str ~equal:String.equal
            || List.exists funcs ~f:(fun f ->
                String.equal f.raven_name lemma_name.pid_str)
          then
            error lemma_name.pid_loc
              (Printf.sprintf "Name %s is already declared" lemma_name.pid_str)
          else
            Ok
              ( lemma_name.pid_str,
                {
                  lemma_raven = lemma_name.pid_str;
                  lemma_constant = false;
                  lemma_generic;
                  lemma_inputs;
                  lemma_implicit_count;
                  lemma_outputs;
                } )
      | _ -> error Location.none "Expected a lemma declaration")
  in
  let* () =
    match List.find_a_dup (List.map all_proof_lemmas ~f:fst) ~compare:String.compare with
    | None -> Ok ()
    | Some x -> error Location.none (Printf.sprintf "Duplicate lemma %s" x)
  in
  let proof_lemmas =
    List.filter all_proof_lemmas ~f:(fun (key, _) -> Option.is_none (scoped_binding key))
    @ List.filter_map scoped_proofs.bindings ~f:(fun binding ->
        match binding.kind with
        | Lemma (S.Proof_lemma declaration) when binding.exported ->
            let inputs, outputs =
              List.split_n binding.public_types (List.length declaration.lemma_params)
            in
            let signature =
              List.Assoc.find_exn all_proof_lemmas binding.backend ~equal:String.equal
            in
            Some
              ( binding.public_key,
                { signature with lemma_inputs = inputs; lemma_outputs = outputs } )
        | _ -> None)
  in
  let lemma_context ?at scope =
    let owners = context_owners at in
    let environment =
      Option.value_map scope ~default:source.env ~f:(fun scope ->
          Source.annotation_env source scope.Proof_scopes.environment)
    in
    let project = Proof_bindings.context_type scoped_proofs ~environment in
    let proof_lemmas =
      List.filter_map (Proof_bindings.local_exports scoped_proofs ~scope)
        ~f:(fun binding ->
          match binding.kind with
          | Lemma (S.Proof_lemma declaration) ->
              let inputs, outputs =
                List.split_n binding.public_types (List.length declaration.lemma_params)
              in
              let signature =
                List.Assoc.find_exn all_proof_lemmas binding.backend ~equal:String.equal
              in
              Some
                ( binding.public_key,
                  { signature with lemma_inputs = inputs; lemma_outputs = outputs } )
          | _ -> None)
      @ proof_lemmas
    in
    let proof_lemmas =
      List.map proof_lemmas ~f:(fun (key, signature) ->
          ( key,
            {
              signature with
              lemma_inputs = List.map signature.lemma_inputs ~f:project;
              lemma_outputs = List.map signature.lemma_outputs ~f:project;
            } ))
    in
    let proof_lemmas =
      List.filter_map scoped_proofs.applications ~f:(fun view ->
          if not (Proof_bindings.application_visible ~owners scoped_proofs ~scope view)
          then None
          else
            Option.map
              (List.Assoc.find all_proof_lemmas view.source.backend ~equal:String.equal)
              ~f:(fun signature ->
                let inputs, outputs =
                  List.split_n view.types (List.length signature.lemma_inputs)
                in
                ( view.key,
                  {
                    signature with
                    lemma_raven = view.backend;
                    lemma_inputs = List.map inputs ~f:project;
                    lemma_outputs = List.map outputs ~f:project;
                  } )))
      @ proof_lemmas
    in
    List.filter_map (Proof_bindings.private_bindings scoped_proofs ~scope)
      ~f:(fun binding ->
        Option.map (List.Assoc.find all_proof_lemmas binding.backend ~equal:String.equal)
          ~f:(fun signature ->
            ( binding.backend,
              {
                signature with
                lemma_raven =
                  Option.value (definition_target binding) ~default:signature.lemma_raven;
              } )))
    @ proof_lemmas
  in
  Ok
    ( {
        checked_views;
        checked_resource_entries;
        logical_declarations;
        all_logical_functions;
        generic_callables =
          List.filter_map (all_logical_functions @ all_proof_lemmas)
            ~f:(fun (_, signature) -> signature.lemma_generic);
        proof_support;
        preds;
        spec_funcs;
        lemma_declarations;
        lemma_context;
        module_parameters;
        private_scoped_inputs;
        proof_env;
      },
      state )
