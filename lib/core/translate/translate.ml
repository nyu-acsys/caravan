(** The translation of OCaml implementations to Raven programs.

    So far: top-level functions on integers, booleans, unit, tuples and variant types,
    with their contracts. A function becomes a procedure, and a variant type a data type
    (see {!Datatypes}). Expressions are put in A-normal form, since a call is a statement
    in Raven; arguments are evaluated right to left, as OCaml does. *)

open Base
open Translate_context
open Proof_terms
open Atomic_proofs
open Procedures
open Program_items
open Proof_declarations

let program (source : Source.t) : (R.Program.t * origin list, error) Result.t =
  let annotations = Annotation.of_comments source.comments in
  (* Each annotation on an atomic step, by the end of the code it follows. *)
  let linearizations =
    List.filter_map annotations ~f:(fun a ->
        if Poly.equal (Annotation.kind a) Annotation.Linearization then
          let rec anchor i =
            if i > 0 && Char.is_whitespace source.text.[i - 1] then anchor (i - 1) else i
          in
          Some (anchor a.loc.loc_start.pos_cnum, a)
        else None)
  in
  (* Each follows an application of an [Atomic] operation. *)
  let typed = without_application_operators source.typed in
  let steps = atomic_steps typed in
  let* initializations = initialization_annotations source typed annotations in
  let* () =
    match
      List.find linearizations ~f:(fun (anchor, _) ->
          not (List.mem steps anchor ~equal:Int.equal))
    with
    | Some (_, a) ->
        error a.loc "This annotation does not follow an atomic step, as Atomic.get t"
    | None -> Ok ()
  in
  let backend_names = Names.create () in
  backend_names.used <-
    Set.of_list
      (module String)
      [
        "Library";
        "List";
        "Option";
        "Seq";
        "FinSet";
        "Set";
        "Map";
        "Int";
        "Real";
        "Bool";
        Prelude.div;
        Prelude.mod_;
        Prelude.in_range;
        Prelude.wrap;
      ];
  let reserved =
    List.map source.libraries ~f:(fun lib -> lib.Source.library_name)
    @ List.map source.proof_types ~f:(fun data -> data.Datatypes.module_name)
    @ List.concat_map source.proof_resources ~f:(fun resource ->
        List.map (resource.Source.resource_descriptor :: resource.resource_aliases)
          ~f:(fun data -> data.Datatypes.module_name))
    @ List.filter_map source.proof ~f:(function
      | S.Proof_function { function_name; _ } -> Some function_name.pid_str
      | Proof_lemma { lemma_name; _ } -> Some lemma_name.pid_str
      | Proof_predicate p -> Some p.pred_name.pid_str
      | Proof_invariant { inv_name; _ } -> Some inv_name.pid_str
      | Proof_view { view_name; _ } -> Some view_name.pid_str
      | _ -> None)
  in
  let declarations ~interface comments =
    List.filter
      (Annotation.of_comments comments)
      ~f:(Annotation.predicate_declaration ~interface)
  in
  let declarations =
    declarations ~interface:false (direct_source_comments source)
    @ Option.value_map source.interface ~default:[] ~f:(fun interface ->
        declarations ~interface:true (direct_interface_comments interface))
  in
  let* declared_predicates = all declarations ~f:Annotation.predicate in
  let reserved =
    reserved @ List.map declared_predicates ~f:(fun p -> p.S.pred_name.pid_str)
  in
  backend_names.used <-
    Set.union backend_names.used (Set.of_list (module String) reserved);
  let fresh = Names.fresh backend_names in
  let source =
    let scoped_types =
      List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
          match entry.Proof_scopes.declaration with
          | S.Proof_type _ when Option.is_some entry.scope.owner ->
              Some entry.name.pid_loc
          | _ -> None)
    in
    {
      source with
      proof_resources =
        List.map source.proof_resources ~f:(fun resource ->
            match resource.Source.resource_scope with
            | None when resource.resource_abstract ->
                let backend = fresh resource.resource_backend in
                {
                  resource with
                  resource_backend = backend;
                  resource_descriptor =
                    Datatypes.with_name resource.resource_descriptor backend;
                }
            | None -> resource
            | Some owner ->
                let namespace =
                  Option.value_map
                    (Proof_scopes.find_owner source.proof_scopes (Some owner)) ~default:[]
                    ~f:(fun scope -> scope.namespace)
                in
                let backend =
                  fresh (String.concat ~sep:"_" (namespace @ [ resource.resource_name ]))
                in
                {
                  resource with
                  resource_backend = backend;
                  resource_descriptor =
                    Datatypes.with_name resource.resource_descriptor backend;
                  resource_public =
                    Option.map resource.resource_public ~f:(fun public ->
                        let backend = fresh ("Export_" ^ backend) in
                        {
                          public with
                          resource_backend = backend;
                          resource_descriptor =
                            Datatypes.with_name public.resource_descriptor backend;
                        });
                });
      proof_fields =
        List.map source.proof_fields ~f:(fun field ->
            match field.Source.field_scope with
            | None -> field
            | Some owner ->
                let namespace =
                  Option.value_map
                    (Proof_scopes.find_owner source.proof_scopes (Some owner)) ~default:[]
                    ~f:(fun scope -> scope.namespace)
                in
                {
                  field with
                  field_backend =
                    fresh
                      (String.uncapitalize
                         (String.concat ~sep:"_" (namespace @ [ field.field_name ])));
                });
      proof_types =
        List.map source.proof_types ~f:(fun data ->
            if List.mem scoped_types data.Datatypes.at ~equal:Poly.equal then
              Datatypes.with_name data (fresh data.module_name)
            else data);
    }
  in
  let resource_implementations =
    List.filter_map source.proof_resources ~f:(fun resource ->
        Option.some_if
          (resource.Source.resource_definition
          && Option.is_none resource.resource_application)
          (resource.resource_id, fresh ("Implementation_" ^ resource.resource_backend)))
  in
  let proof_implementations =
    List.filter_map source.proof_resources ~f:(fun resource ->
        Option.some_if
          (resource.Source.resource_definition
          && Option.is_none resource.resource_application)
          (resource.resource_id, fresh ("Proofs_" ^ resource.resource_backend)))
  in
  let implementation resource =
    List.Assoc.find resource_implementations resource.Source.resource_id ~equal:Ident.same
  in
  let proof_implementation resource =
    List.Assoc.find proof_implementations resource.Source.resource_id ~equal:Ident.same
  in
  let definition_resource scope =
    Option.bind scope.Proof_scopes.owner ~f:(fun owner ->
        List.find source.proof_resources ~f:(fun resource ->
            resource.resource_definition
            && (Path.same owner resource.resource_path
               || Path.same owner (Path.Pident resource.resource_id))))
  in
  let definition_target (binding : Proof_bindings.binding) =
    Option.bind (definition_resource binding.entry.scope) ~f:(fun resource ->
        let backend =
          match binding.kind with
          | Predicate _ | Lemma _ -> proof_implementation resource
          | Function _ | Resource _ | Field _ | Atomic _ | State _ | Action _ ->
              implementation resource
        in
        Option.map backend ~f:(fun backend -> backend ^ "." ^ binding.entry.name.pid_str))
  in
  let* inventory = Module_inventory.build source typed in
  let* scoped_proofs = Proof_bindings.build ~fresh source inventory in
  let scoped_binding name =
    List.find scoped_proofs.bindings ~f:(fun binding -> String.equal binding.backend name)
  in
  let declaration_scope name =
    Option.map (scoped_binding name) ~f:(fun binding -> binding.entry.scope)
  in
  let declaration_environment name =
    Option.value_map (scoped_binding name) ~default:source.env ~f:(fun binding ->
        binding.environment)
  in
  let definition_member_name name =
    Option.bind (scoped_binding name) ~f:(fun binding ->
        Option.map (definition_target binding) ~f:(fun _ -> binding.entry.name.pid_str))
  in
  let typed = inventory.structure in
  let* libraries = Library_modules.flatten ~fresh source.libraries in

  List.iter libraries ~f:(fun lib ->
      List.iter lib.Library_modules.library.signature ~f:(fun item ->
          match item.Parsetree.psig_desc with
          | Psig_type (_, decls) ->
              List.iter decls ~f:(fun decl ->
                  backend_names.used <-
                    Set.add backend_names.used
                      (lib.library_name ^ "_" ^ decl.Parsetree.ptype_name.txt))
          | _ -> ()));
  let* types, funcs = items source ~fresh inventory in
  let* lifted = all funcs ~f:(fun f -> local_functions ~source f annotations) in
  let lifted =
    List.map (List.concat lifted) ~f:(fun f -> { f with raven_name = fresh f.raven_name })
  in
  let funcs = inherit_contracts (funcs @ lifted) in
  let* access_proofs =
    access_annotations ~libraries
      ~checked:
        (List.concat_map inventory.bindings ~f:(fun binding ->
             List.concat_map binding.Module_inventory.paths ~f:(fun path ->
                 List.map binding.expected.signature_values ~f:(fun (member, _) ->
                     Path.Pdot (path, member)))))
      source typed annotations ~functions:funcs
  in
  let state_targets = ref [] and nested_reads = ref [] in
  let remember (e : Typedtree.expression) =
    state_targets :=
      (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum) :: !state_targets
  in
  let rec lexical_tail (e : Typedtree.expression) =
    remember e;
    match e.exp_desc with
    | Texp_let (_, _, body) | Texp_sequence (_, body) -> lexical_tail body
    | Texp_ifthenelse (_, yes, no) ->
        lexical_tail yes;
        Option.iter no ~f:lexical_tail
    | Texp_match (_, cases, _, _) ->
        List.iter cases ~f:(fun c -> lexical_tail c.Typedtree.c_rhs)
    | _ -> ()
  in
  let visit iterator (e : Typedtree.expression) =
    if Option.is_some (atomic_read_argument e) then nested_reads := e :: !nested_reads;
    begin match e.exp_desc with
    | Texp_let (Nonrecursive, [ binding ], body) ->
        remember binding.vb_expr;
        lexical_tail body
    | Texp_let (_, _, body) -> lexical_tail body
    | Texp_sequence (left, right) ->
        remember left;
        lexical_tail right
    | Texp_ifthenelse (_, yes, no) ->
        lexical_tail yes;
        Option.iter no ~f:lexical_tail
    | Texp_match (_, cases, _, _) ->
        List.iter cases ~f:(fun c -> lexical_tail c.Typedtree.c_rhs)
    | Texp_while (_, body) | Texp_for (_, _, _, _, _, body) -> lexical_tail body
    | _ -> ()
    end;
    Tast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Tast_iterator.default_iterator with expr = visit } in
  List.iter funcs ~f:(fun f ->
      lexical_tail f.body;
      iterator.expr iterator f.body);
  let* () =
    Result.all_unit
      (List.map !nested_reads ~f:(fun e ->
           let* argument = nested_stateful_read access_proofs e in
           Option.iter argument ~f:(fun argument ->
               remember e;
               remember argument);
           Ok ()))
  in
  let* () =
    Result.all_unit
      (List.map access_proofs ~f:(fun (key, a) ->
           let* scope = Annotation.scope a in
           if
             Option.is_some scope.scope_state
             && not (List.mem !state_targets key ~equal:Poly.equal)
           then
             error a.loc
               "A stateful scope needs a direct let binding, sequence continuation, \
                lexical tail, or directly nested stateful read"
           else Ok ()))
  in
  let tails = ref [] in
  let rec collect_tail (e : Typedtree.expression) =
    tails := (e.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum) :: !tails;
    match e.exp_desc with
    | Texp_let (_, _, body) | Texp_sequence (_, body) -> collect_tail body
    | Texp_ifthenelse (_, yes, no) ->
        collect_tail yes;
        Option.iter no ~f:collect_tail
    | Texp_match (_, cases, _, _) ->
        List.iter cases ~f:(fun c -> collect_tail c.Typedtree.c_rhs)
    | _ -> ()
  in
  List.iter funcs ~f:(fun f -> collect_tail f.body);
  let* return_proofs =
    attached_annotations ~all_expressions:true ~innermost:true source typed annotations
      ~kind:Annotation.Returns
      ~is_target:(fun e ->
        List.mem !tails
          (e.Typedtree.exp_loc.loc_start.pos_cnum, e.exp_loc.loc_end.pos_cnum)
          ~equal:Poly.equal)
      ~description:"Ghost.returns must follow a normal tail expression"
  in
  let* () =
    Result.all_unit
      (List.map (access_proofs @ return_proofs) ~f:(fun ((start, finish), annotation) ->
           let owners =
             List.filter funcs ~f:(fun f ->
                 start >= f.body.exp_loc.loc_start.pos_cnum
                 && finish <= f.body.exp_loc.loc_end.pos_cnum)
           in
           match
             List.min_elt owners ~compare:(fun a b ->
                 Int.compare
                   (a.body.exp_loc.loc_end.pos_cnum - a.body.exp_loc.loc_start.pos_cnum)
                   (b.body.exp_loc.loc_end.pos_cnum - b.body.exp_loc.loc_start.pos_cnum))
           with
           | Some f when f.manual && not f.trusted -> Ok ()
           | Some f when f.trusted ->
               error annotation.loc "Ghost.scope cannot be used in a trusted function"
           | _ -> error annotation.loc "Ghost.scope requires a manual function proof"))
  in
  (* The abstract types of the libraries. *)
  let* library_types =
    all libraries ~f:(fun (lib : Library_modules.t) ->
        all lib.library.signature ~f:(fun (item : Parsetree.signature_item) ->
            match item.psig_desc with
            | Psig_type (_, decls) ->
                all decls ~f:(fun (decl : Parsetree.type_declaration) ->
                    match (decl.ptype_kind, decl.ptype_manifest, decl.ptype_params) with
                    | Ptype_abstract, None, [] ->
                        Ok
                          ( Datatypes.library_type ~library:lib.library_name
                              ~library_id:lib.library_id ~at:decl.ptype_loc
                              decl.ptype_name.txt
                          |> fun descriptor ->
                            Datatypes.with_paths descriptor
                              [ Path.Pdot (lib.library_path, decl.ptype_name.txt) ] )
                    | _ ->
                        unsupported decl.ptype_loc
                          "A type of a library other than an abstract one without \
                           parameters")
            | _ -> Ok []))
  in
  let types = List.concat (List.concat library_types) @ types @ source.proof_types in
  let rec alias_path ~target ~alias path =
    if Path.same target path then Some alias
    else
      match path with
      | Path.Pdot (parent, name) ->
          Option.map (alias_path ~target ~alias parent) ~f:(fun parent ->
              Path.Pdot (parent, name))
      | Papply (head, argument) ->
          let head_alias = alias_path ~target ~alias head in
          let argument_alias = alias_path ~target ~alias argument in
          if Option.is_none head_alias && Option.is_none argument_alias then None
          else
            Some
              (Path.Papply
                 ( Option.value head_alias ~default:head,
                   Option.value argument_alias ~default:argument ))
      | Pident _ | Pextra_ty _ -> None
  in
  let types =
    List.map types ~f:(fun data ->
        let declared =
          data.Datatypes.paths @ Option.to_list data.library
          @ Option.to_list (Option.map data.id ~f:(fun id -> Path.Pident id))
        in
        let rec expand remaining paths =
          let aliases =
            List.concat_map inventory.aliases ~f:(fun (alias, target) ->
                List.filter_map paths ~f:(alias_path ~target ~alias))
          in
          let expanded = Datatypes.with_paths data (paths @ aliases) in
          if remaining = 0 || List.length expanded.paths = List.length paths then expanded
          else expand (remaining - 1) expanded.paths
        in
        expand (List.length inventory.aliases) declared)
  in
  let* types =
    List.fold_result inventory.bindings ~init:types ~f:(fun types binding ->
        List.fold_result binding.Module_inventory.expected.signature_types ~init:types
          ~f:(fun types (member, declaration) ->
            let actual = Path.Pdot (binding.actual_path, member) in
            match Datatypes.find types actual with
            | None ->
                unsupported declaration.Typedtree.typ_loc
                  "A checked module type without a supported representation"
            | Some descriptor ->
                let aliases =
                  List.map binding.paths ~f:(fun path -> Path.Pdot (path, member))
                in
                Ok
                  (List.map types ~f:(fun data ->
                       if phys_equal data descriptor then
                         Datatypes.with_paths data aliases
                       else data))))
  in
  let public_types =
    List.concat_map inventory.bindings ~f:(fun binding ->
        List.concat_map binding.Module_inventory.expected.signature_types
          ~f:(fun (member, _) ->
            List.map binding.paths ~f:(fun path -> Path.Pdot (path, member))))
  in
  let* generics = generic_modules source ~fresh ~types ~functions:funcs inventory in
  let* module_scopes = Module_context.collect_scopes source.proof_scopes in
  let* generic_proofs = Generic_proofs.plan generics module_scopes in
  let module_contexts = Module_context.plan ~scopes:module_scopes generic_proofs in
  let declaration_context name =
    Module_context.for_scope module_contexts (declaration_scope name)
  in
  let asset_context owner = Module_context.for_owner module_contexts owner in
  let context_for_group group =
    Option.value
      (Module_context.for_group module_contexts group)
      ~default:module_contexts.root
  in
  let* generic_proof_types =
    all generic_proofs ~f:Generic_proofs.types |> Result.map ~f:List.concat
  in
  let* _ =
    all scoped_proofs.bindings ~f:(fun binding ->
        if
          Option.is_none
            (Proof_bindings.functor_ancestor source.proof_scopes binding.entry.scope)
          || Option.is_some
               (Generic_proofs.owner generic_proofs (Some binding.entry.scope))
        then Ok ()
        else
          unsupported binding.entry.name.pid_loc
            "A functor proof without a supported generic runtime body and application")
  in
  let* _ =
    all source.proof_types ~f:(fun data ->
        match Generic_proofs.model_owner source data with
        | Some scope
          when Option.is_some (Proof_bindings.functor_ancestor source.proof_scopes scope)
               && Option.is_none (Generic_proofs.owner generic_proofs (Some scope)) ->
            unsupported data.Datatypes.at
              "A functor proof without a supported generic runtime body and application"
        | Some _ | None -> Ok ())
  in
  let proof_worker name = (declaration_context name).worker in
  let* applications =
    Generic_proofs.applications ~fresh source inventory scoped_proofs generic_proofs
  in
  let scoped_proofs = Proof_bindings.with_applications scoped_proofs applications in
  let asset_worker owner = (asset_context owner).worker in
  let source =
    let project_descriptor context backend abstract_member descriptor =
      if List.is_empty context.Module_context.namespace then descriptor
      else
        let descriptor =
          List.fold (Option.value_map abstract_member ~default:[] ~f:fst) ~init:descriptor
            ~f:(fun descriptor parameter ->
              match abstract_member with
              | Some (_, member) ->
                  Datatypes.with_paths descriptor
                    [ Path.Pdot (Path.Pdot (Path.Pident parameter, member), "t") ]
              | None -> descriptor)
        in
        {
          descriptor with
          Datatypes.module_name = backend;
          module_path = Some (String.split backend ~on:'.');
          backend_type =
            Some Qualified_name.{ path = String.split backend ~on:'.'; name = "T" };
        }
    in
    {
      source with
      proof_resources =
        List.map source.proof_resources ~f:(fun resource ->
            let context = asset_context resource.Source.resource_scope in
            let parameter =
              if resource.resource_abstract then
                List.find context.parameters ~f:(fun parameter ->
                    Option.exists parameter.Generic_proofs.original ~f:(fun original ->
                        Source.resource_has_path resource
                          (Path.Pdot (Path.Pident original, resource.resource_name))))
              else None
            in
            let backend =
              Module_context.member context
                (Option.value_map parameter ~default:resource.resource_backend
                   ~f:(fun parameter ->
                     parameter.generic.parameter ^ "." ^ resource.resource_name))
            in
            let abstract_member =
              Option.map parameter ~f:(fun parameter ->
                  ( Option.to_list parameter.original @ [ parameter.instance.parameter ],
                    resource.resource_name ))
            in
            {
              resource with
              resource_backend = backend;
              resource_descriptor =
                project_descriptor context backend abstract_member
                  resource.resource_descriptor;
              resource_aliases =
                List.map resource.resource_aliases
                  ~f:(project_descriptor context backend None);
              resource_public =
                Option.map resource.resource_public ~f:(fun public ->
                    let backend = Module_context.member context public.resource_backend in
                    {
                      public with
                      resource_backend = backend;
                      resource_descriptor =
                        project_descriptor context backend None public.resource_descriptor;
                    });
            });
      proof_fields =
        List.map source.proof_fields ~f:(fun field ->
            let context = asset_context field.Source.field_scope in
            {
              field with
              field_backend = Module_context.member context field.field_backend;
            });
    }
  in
  let resource_views resource =
    resource :: Option.to_list resource.Source.resource_public
  in
  let application_resources =
    Generic_proofs.resource_applications source inventory generic_proofs
    |> List.map ~f:(fun resource ->
        match
          List.find source.proof_resources ~f:(fun view ->
              Option.is_some view.Source.resource_application
              && Path.same view.resource_path resource.Source.resource_path)
        with
        | None -> resource
        | Some view ->
            {
              resource with
              resource_id = view.resource_id;
              resource_application = view.resource_application;
              resource_public =
                Option.map resource.resource_public ~f:(fun public ->
                    Option.value_map view.resource_public ~default:public ~f:(fun view ->
                        { public with resource_id = view.resource_id }));
            })
  in
  let all_resources =
    application_resources
    @ List.filter source.proof_resources ~f:(fun r ->
        Option.is_none r.Source.resource_application)
  in
  let all_resource_views = List.concat_map all_resources ~f:resource_views in
  let resource_binding resource =
    List.find scoped_proofs.bindings ~f:(fun binding ->
        match binding.Proof_bindings.kind with
        | Resource actual -> Ident.same actual.resource_id resource.Source.resource_id
        | _ -> false)
  in
  let resource_view ~scope resource =
    match resource_binding resource with
    | Some binding when Proof_bindings.opaque_at scoped_proofs ~scope binding ->
        Option.value resource.resource_public ~default:resource
    | None ->
        begin match
          List.find scoped_proofs.applications ~f:(fun view ->
              Path.same
                (Path.Pdot (view.Proof_bindings.path, view.source.entry.name.pid_str))
                resource.Source.resource_path)
        with
        | Some view when Proof_bindings.application_opaque scoped_proofs ~scope view ->
            Option.value resource.resource_public ~default:resource
        | Some _ | None -> resource
        end
    | Some _ -> resource
  in
  let private_ra_types =
    List.filter_map source.proof_types ~f:(fun data ->
        Option.bind (Generic_proofs.model_owner source data) ~f:(fun scope ->
            if Option.is_none scope.Proof_scopes.definition then None
            else
              Option.map (Generic_proofs.owner generic_proofs (Some scope))
                ~f:(fun plan ->
                  let backend = plan.group.name ^ "." ^ data.Datatypes.module_name in
                  ( plan,
                    {
                      data with
                      module_path = Some (String.split backend ~on:'.');
                      backend_type =
                        Some
                          Qualified_name.
                            { path = String.split backend ~on:'.'; name = "T" };
                    } ))))
  in
  let proof_assets scope =
    let environment =
      Option.value_map scope ~default:source.env ~f:(fun scope ->
          Source.annotation_env source scope.Proof_scopes.environment)
    in
    let rebase = Proof_bindings.context_type scoped_proofs ~environment in
    let private_owner owner =
      match (owner, scope) with
      | None, _ -> true
      | Some owner, Some caller ->
          Option.exists (Proof_scopes.find_owner source.proof_scopes (Some owner))
            ~f:(fun owner ->
              Option.is_some
                (Proof_bindings.drop_prefix owner.namespace caller.Proof_scopes.namespace))
      | Some _, None -> false
    in
    let project owner typ =
      if private_owner owner then typ
      else rebase (Proof_bindings.public_type scoped_proofs typ)
    in
    let visible entry =
      Option.value_map entry ~default:true
        ~f:(Proof_bindings.visible scoped_proofs ~scope)
    in
    let resources =
      List.filter_map
        (List.filter source.proof_resources ~f:(fun resource ->
             Option.is_none resource.Source.resource_application))
        ~f:(fun resource ->
          let binding =
            List.find scoped_proofs.bindings ~f:(fun binding ->
                match binding.kind with
                | Resource actual ->
                    Ident.same actual.resource_id resource.Source.resource_id
                | _ -> false)
          in
          if not (visible binding) then None
          else
            let resource = resource_view ~scope resource in
            let project = project resource.resource_scope in
            Some
              {
                resource with
                resource_type = project resource.resource_type;
                resource_operations =
                  List.map resource.resource_operations ~f:(fun (name, inputs, output) ->
                      (name, List.map inputs ~f:project, project output));
              })
    in
    let fields =
      List.filter_map source.proof_fields ~f:(fun field ->
          let binding =
            List.find scoped_proofs.bindings ~f:(fun binding ->
                match binding.kind with
                | Field actual -> Ident.same actual.field_id field.Source.field_id
                | _ -> false)
          in
          if not (visible binding) then None
          else
            let project = project field.field_scope in
            Some
              {
                field with
                field_owner = project field.field_owner;
                field_value = project field.field_value;
              })
    in
    let application_resources =
      List.filter_map application_resources ~f:(fun resource ->
          let view =
            List.find scoped_proofs.applications ~f:(fun view ->
                Path.same
                  (Path.Pdot (view.Proof_bindings.path, view.source.entry.name.pid_str))
                  resource.Source.resource_path)
          in
          match view with
          | Some view when Proof_bindings.application_visible scoped_proofs ~scope view ->
              Some
                (if Proof_bindings.application_opaque scoped_proofs ~scope view then
                   Option.value resource.resource_public ~default:resource
                 else resource)
          | Some _ | None -> None)
    in
    let application_fields =
      List.filter_map scoped_proofs.applications ~f:(fun view ->
          match view.Proof_bindings.source.kind with
          | Field original
            when Proof_bindings.application_visible scoped_proofs ~scope view ->
              Option.map
                (List.find source.proof_fields ~f:(fun field ->
                     Ident.same field.Source.field_id original.field_id))
                ~f:(fun field ->
                  let prefix = (Qualified_name.of_string view.backend).path in
                  let leaf = (Qualified_name.of_string field.field_backend).name in
                  {
                    field with
                    field_path = Path.Pdot (view.path, field.field_name);
                    field_backend = String.concat ~sep:"." (prefix @ [ leaf ]);
                    field_owner = view.project_type field.field_owner;
                    field_value = view.project_type field.field_value;
                    field_resource =
                      Option.map field.field_resource ~f:(fun owner ->
                          match
                            Types.get_desc
                              (view.project_type
                                 (Ctype.newconstr (Path.Pdot (owner, "t")) []))
                          with
                          | Tconstr (Path.Pdot (owner, "t"), [], _) -> owner
                          | _ -> owner);
                  })
          | _ -> None)
    in
    (resources @ application_resources, fields @ application_fields)
  in
  let layouts = Result_layouts.plan types generics in
  let* types = Result_layouts.concrete layouts types in
  let schema binding =
    Option.map (Generic_modules.application_for_binding generics binding)
      ~f:(fun (group, application) ->
        Checked_modules.
          {
            interface = Generic_modules.interface group application;
            members = group.operations;
          })
  in
  let checked_modules = Checked_modules.plan ~schema ~fresh inventory.bindings in
  let* checked_operations =
    all checked_modules ~f:(fun view ->
        let binding = view.Checked_modules.binding in
        all binding.Module_inventory.expected.signature_values
          ~f:(fun (member, signature) ->
            let* contract = signature_contract signature in
            let* () =
              match contract with
              | Some c when c.S.pure || Option.is_some c.continues ->
                  unsupported signature.site.item_loc
                    "A pure or continuation contract in a checked module view"
              | _ -> Ok ()
            in
            let operation_member =
              List.Assoc.find_exn view.members member ~equal:String.equal
            in
            Ok
              {
                operation_binding = binding;
                operation_signature = signature;
                operation_contract = contract;
                operation_name =
                  (if view.grouped then view.name ^ "." ^ operation_member
                   else operation_member);
                operation_member;
                operation_paths =
                  List.map binding.paths ~f:(fun path -> Path.Pdot (path, member));
              }))
  in
  let checked_operations = List.concat checked_operations in

  (* The data types, and the sequences of specifications, which have no module. *)
  let* inferred_pure = pure_functions funcs in
  let pure =
    inferred_pure
    @ List.filter funcs ~f:(fun f ->
        let inferred id =
          List.exists inferred_pure ~f:(fun pure -> Ident.same pure.id id)
        in
        (not (inferred f.id))
        && Option.exists (Generic_modules.member generics f.id)
             ~f:(fun (group, _, stem) ->
               List.exists group.applications ~f:(fun application ->
                   List.exists application.source.body_members ~f:(fun (source, id) ->
                       String.equal
                         (List.Assoc.find_exn group.body_members source
                            ~equal:String.equal)
                         stem
                       && inferred id))))
  in
  let is_pure (f : func) = List.exists pure ~f:(fun g -> Ident.same g.id f.id) in
  let generic_procedures =
    List.concat_map generics ~f:(fun group ->
        List.map group.body_members ~f:(fun (source, stem) ->
            let id =
              List.Assoc.find_exn group.representative.body_members source
                ~equal:String.equal
            in
            let f = List.find_exn funcs ~f:(fun f -> Ident.same f.id id) in
            (group.name ^ "." ^ stem, if is_pure f then fresh (stem ^ "_impl") else stem)))
  in
  let procedure_stem group stem =
    List.Assoc.find_exn generic_procedures
      (group.Generic_modules.name ^ "." ^ stem)
      ~equal:String.equal
  in
  let pure_name f =
    match Generic_modules.member generics f.id with
    | None -> f.raven_name
    | Some (_, application, stem) -> application.name ^ "." ^ stem
  in
  let pure_reference f =
    match Generic_modules.member generics f.id with
    | None -> Qualified_name.{ path = []; name = f.raven_name }
    | Some _ -> Qualified_name.of_string (pure_name f)
  in
  let procedures =
    List.map funcs ~f:(fun f ->
        let name =
          match Generic_modules.member generics f.id with
          | None -> if is_pure f then fresh (f.raven_name ^ "_impl") else f.raven_name
          | Some (group, application, stem) ->
              application.name ^ "." ^ procedure_stem group stem
        in
        (f.id, name))
  in
  let proc_name (f : func) = List.Assoc.find_exn procedures f.id ~equal:Ident.same in
  let body_proc_name f =
    match Generic_modules.member generics f.id with
    | None -> proc_name f
    | Some (group, _, stem) -> group.name ^ "." ^ procedure_stem group stem
  in
  let body_pure_name f =
    match Generic_modules.member generics f.id with
    | None -> pure_name f
    | Some (group, _, stem) -> group.name ^ "." ^ stem
  in
  let body_pure_reference f =
    match Generic_modules.member generics f.id with
    | None -> pure_reference f
    | Some _ -> Qualified_name.of_string (body_pure_name f)
  in
  let body_owner f =
    match Generic_modules.member generics f.id with
    | None -> None
    | Some (group, application, _) ->
        Some (group, phys_equal application.source group.representative)
  in
  let body_module_context f =
    match body_owner f with
    | Some (group, _) -> context_for_group group
    | None -> Module_context.for_location module_contexts f.loc
  in
  let body_destination f =
    match body_owner f with
    | None -> (body_module_context f).destination
    | Some (group, _) -> Module_context.Worker group
  in
  let runtime_destinations =
    Module_context.Flat :: List.map generics ~f:(fun group -> Module_context.Worker group)
  in
  let with_body_names entries =
    entries
    @ List.filter_map funcs ~f:(fun f ->
        match body_owner f with
        | Some (_, true) ->
            Option.map
              (List.Assoc.find entries (proc_name f) ~equal:String.equal)
              ~f:(fun value -> (body_proc_name f, value))
        | Some (_, false) | None -> None)
  in
  let* procedure_signatures =
    all funcs ~f:(fun f ->
        let outputs = ghost_results f in
        let* () =
          match outputs with
          | (id, _) :: _ when is_pure f ->
              unsupported id.pid_loc "Ghost results of a pure function"
          | (id, _) :: _ when not f.manual ->
              unsupported id.pid_loc "Ghost results require a manual function proof"
          | _ -> Ok ()
        in
        let declared xs =
          all xs ~f:(fun (id, pty) ->
              let* t = Source.ocaml_type f.environment ~at:id.S.pid_loc pty in
              Ok (id.pid_str, t))
        in
        let* procedure_inputs = declared (ghost_params f) in
        let* procedure_outputs = declared outputs in
        Ok
          ( proc_name f,
            { procedure_inputs; procedure_outputs; procedure_result = f.body.exp_type } ))
  in
  let procedure_signatures = with_body_names procedure_signatures in
  let au_plan (au : Source.proof_au) =
    if Option.is_none au.au_application then asset_worker au.au_scope else None
  in
  let au_procedure au f =
    match au_plan au with Some _ -> body_proc_name f | None -> proc_name f
  in
  let au_application_view (au : Source.proof_au) =
    Option.bind au.au_application ~f:(fun (_, template) ->
        List.find scoped_proofs.applications ~f:(fun view ->
            match view.source.kind with
            | Atomic original ->
                Ident.same original.au_id template
                && Path.same au.au_path (Path.Pdot (view.path, au.au_name))
            | _ -> false))
  in
  let applied_atomic_operation (au : Source.proof_au) =
    let ( let* ) value f = Option.bind value ~f in
    let* identity, template = au.au_application in
    let* binding =
      List.find scoped_proofs.bindings ~f:(fun binding ->
          match binding.Proof_bindings.kind with
          | Atomic original -> Ident.same original.au_id template
          | _ -> false)
    in
    let* plan = Generic_proofs.owner generic_proofs (Some binding.entry.scope) in
    let* operation =
      match binding.kind with
      | Atomic original -> Some original.au_operation_path
      | _ -> None
    in
    let* application =
      List.find plan.group.applications ~f:(fun application ->
          Path.same application.source.identity identity)
    in
    let* id = Generic_proofs.function_id plan ~instance:application.source operation in
    List.find funcs ~f:(fun f -> Ident.same f.id id)
  in
  let* atomic_operations =
    all source.proof_aus ~f:(fun (au : Source.proof_au) ->
        let operation =
          match au_plan au with
          | None ->
              Option.first_some
                (List.find funcs ~f:(fun f ->
                     List.mem f.paths au.au_operation_path ~equal:Path.same))
                (applied_atomic_operation au)
          | Some plan ->
              Option.bind (Generic_proofs.function_id plan au.au_operation_path)
                ~f:(fun id -> List.find funcs ~f:(fun f -> Ident.same f.id id))
        in
        match operation with
        | None ->
            error au.au_at "An AU facade must name a procedure in this implementation"
        | Some f when not (Option.exists f.contract ~f:(fun c -> c.atomic)) ->
            error au.au_at "An AU facade requires a logically atomic contract"
        | Some f -> Ok (au, f))
  in
  let token_types =
    List.map atomic_operations ~f:(fun (au, f) ->
        Datatypes.with_paths
          (Datatypes.atomic_token ~path:au.Source.au_token_path
             ~procedure:(au_procedure au f) ~at:au.au_at)
          au.au_token_paths)
  in
  let generic_models = Generic_proofs.model_types source inventory generic_proofs in
  let generic_model data =
    List.exists generic_proofs ~f:(fun plan ->
        List.exists (Generic_proofs.models source plan) ~f:(fun model ->
            Poly.equal model.Datatypes.at data.Datatypes.at))
  in
  let private_ra_type data =
    List.exists private_ra_types ~f:(fun (_, owned) ->
        Poly.equal data.Datatypes.at owned.Datatypes.at)
  in
  let data_types =
    List.filter types ~f:(fun data ->
        (not (generic_model data)) && not (private_ra_type data))
  in
  let resource_types =
    List.concat_map all_resource_views ~f:(fun r ->
        r.Source.resource_descriptor :: r.resource_aliases)
  in
  let* generic_runtime_types =
    all generic_proofs ~f:(fun plan ->
        let* layouts =
          Result_layouts.symbolic layouts plan.Generic_proofs.group
            ~owner:(String.split plan.group.name ~on:'.' @ [ "Layout" ])
        in
        Ok
          (List.filter_map (Generic_proofs.runtime_types plan) ~f:(fun declaration ->
               Option.map
                 (List.find layouts ~f:(fun descriptor ->
                      Option.exists descriptor.Datatypes.id ~f:(fun id ->
                          String.equal (Ident.name id) declaration.Typedtree.typ_name.txt)
                      && Poly.equal descriptor.at declaration.typ_loc))
                 ~f:(fun descriptor ->
                   {
                     descriptor with
                     id = Some declaration.typ_id;
                     paths = [];
                     library = None;
                   }))))
    |> Result.map ~f:List.concat
  in
  let types =
    generic_runtime_types
    @ List.map private_ra_types ~f:snd
    @ generic_models @ generic_proof_types @ types @ resource_types @ token_types
    @ source.logical_types
    @ match source.sequence with Pident id -> [ Datatypes.sequence id ] | _ -> []
  in
  (* Each data type's module, given the ones declared before it; a record type that is a
     reference has fields instead. *)
  let* modules =
    all
      (List.filter_mapi data_types ~f:(fun i (d : Datatypes.t) ->
           Option.some_if
             (Option.is_none d.heap && Option.is_none d.alias
             && not (Result_layouts.contains layouts d))
             (List.take data_types i, d)))
      ~f:(fun (before, d) ->
        let* member =
          Datatypes.member
            (generic_proof_types @ generic_models @ before @ resource_types @ token_types
           @ source.logical_types)
            d
        in
        Ok (d.Datatypes.module_name, member))
  in
  let proof_module path ~at =
    match
      List.find all_resources ~f:(fun resource -> Source.resource_has_path resource path)
    with
    | Some resource -> Ok resource
    | None -> error at "The proof module argument has no translated declaration"
  in
  let rec depends_on_definition seen resource =
    if Option.is_some resource.Source.resource_application then false
    else if List.mem seen resource.resource_id ~equal:Ident.same then false
    else if resource.resource_definition then true
    else
      let seen = resource.resource_id :: seen in
      let dependency path =
        List.exists source.proof_resources ~f:(fun argument ->
            (Path.same path argument.resource_path
            || Path.same path (Path.Pident argument.resource_id))
            && depends_on_definition seen argument)
      in
      Option.exists resource.resource_alias_of ~f:dependency
      || List.exists resource.resource_arguments ~f:(function
        | Source.Type_argument _ -> false
        | Module_argument path -> dependency path)
  in
  let deferred_resources =
    List.filter source.proof_resources ~f:(fun resource ->
        Option.is_none resource.Source.resource_application
        && Module_context.emits_owner module_contexts ~destination:Module_context.Flat
             resource.resource_scope
        && depends_on_definition [] resource)
  in
  let* native_resource_members =
    all
      (List.filter source.proof_resources ~f:(fun resource ->
           (not resource.Source.resource_abstract)
           && Option.is_none resource.resource_application))
      ~f:(fun resource ->
        let at = resource.Source.resource_at in
        let l = loc at in
        let* member =
          match (resource.resource_definition, resource.resource_alias_of) with
          | true, _ ->
              let* backend =
                match implementation resource with
                | Some backend -> Ok backend
                | None -> error at "Missing resource algebra implementation"
              in
              let interface =
                qualified_name ~loc:l (String.concat ~sep:"." resource.resource_functor)
              in
              Ok
                (R.Member.alias ~loc:l ~typ:interface ~sealed:true
                   (ident ~loc:l (Qualified_name.of_string resource.resource_backend).name)
                   (qualified_name ~loc:l backend))
          | false, Some path ->
              let* target = proof_module path ~at in
              Ok
                (R.Member.alias ~loc:l
                   (ident ~loc:l (Qualified_name.of_string resource.resource_backend).name)
                   (qualified_name ~loc:l target.resource_backend))
          | false, None ->
              let* arguments =
                all resource.resource_arguments ~f:(function
                  | Source.Type_argument typ -> Datatypes.typ types ~at typ
                  | Module_argument path ->
                      let* argument = proof_module path ~at in
                      Ok
                        (R.Type.named ~loc:l
                           (qualified_name ~loc:l argument.resource_backend)
                           []))
              in
              let library =
                qualified_name ~loc:l (String.concat ~sep:"." resource.resource_functor)
              in
              Ok
                (R.Member.instance ~loc:l ~def:(library, arguments)
                   (ident ~loc:l (Qualified_name.of_string resource.resource_backend).name)
                   library)
        in
        Ok (resource.resource_backend, member))
  in
  let imported_resource_members =
    List.filter_map source.proof_resources ~f:(fun resource ->
        if
          resource.Source.resource_abstract
          && Option.is_none resource.resource_scope
          && Option.is_none resource.resource_application
        then
          let l = loc resource.resource_at in
          Some
            (R.Member.free
               (R.Member.instance ~loc:l
                  (ident ~loc:l resource.resource_backend)
                  (qualified_name ~loc:l
                     (String.concat ~sep:"." resource.resource_functor))))
        else None)
  in
  let public_resource_members =
    List.filter_map
      (List.filter source.proof_resources ~f:(fun resource ->
           Option.is_none resource.Source.resource_application))
      ~f:(fun resource ->
        Option.map resource.Source.resource_public ~f:(fun public ->
            let l = loc public.resource_at in
            ( resource,
              R.Member.alias ~loc:l
                ~typ:
                  (qualified_name ~loc:l (String.concat ~sep:"." public.resource_functor))
                (ident ~loc:l (Qualified_name.of_string public.resource_backend).name)
                (qualified_name ~loc:l resource.resource_backend) )))
  in
  let proof_module_names =
    List.map source.proof_types ~f:(fun data -> data.Datatypes.module_name)
  in
  let runtime_modules =
    List.filter_map modules ~f:(fun (name, member) ->
        Option.some_if (not (List.mem proof_module_names name ~equal:String.equal)) member)
  in
  let proof_modules =
    List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
        match entry.Proof_scopes.declaration with
        | S.Proof_type _ ->
            Option.bind
              (List.find source.proof_types ~f:(fun data ->
                   Poly.equal data.Datatypes.at entry.name.pid_loc))
              ~f:(fun data ->
                List.Assoc.find modules data.module_name ~equal:String.equal)
        | Proof_resource _ ->
            Option.bind
              (List.find source.proof_resources ~f:(fun resource ->
                   Poly.equal resource.Source.resource_at entry.name.pid_loc
                   && Module_context.emits_owner module_contexts
                        ~destination:Module_context.Flat resource.resource_scope
                   && not (depends_on_definition [] resource)))
              ~f:(fun resource ->
                List.Assoc.find native_resource_members resource.resource_backend
                  ~equal:String.equal)
        | _ -> None)
  in
  let deferred_native_resource_members =
    List.filter_map deferred_resources ~f:(fun resource ->
        List.Assoc.find native_resource_members resource.resource_backend
          ~equal:String.equal)
  in
  let rec resource_dependencies seen resource =
    let application =
      List.find_map generics ~f:(fun group ->
          List.find_map group.Generic_modules.applications ~f:(fun application ->
              Option.some_if
                (List.is_prefix
                   (String.split resource.Source.resource_backend ~on:'.')
                   ~prefix:[ application.name ] ~equal:String.equal)
                application.name))
    in
    if Option.is_some application then Ok (Option.to_list application)
    else if List.mem seen resource.Source.resource_id ~equal:Ident.same then Ok []
    else
      let* aliases =
        match resource.resource_alias_of with
        | None -> Ok []
        | Some path ->
            let* target = proof_module path ~at:resource.resource_at in
            resource_dependencies (resource.resource_id :: seen) target
      in
      let* dependencies =
        all resource.resource_arguments ~f:(function
          | Source.Type_argument typ ->
              Ok
                (Result_layouts.type_dependencies
                   ~additional:(Generic_proofs.layout_dependencies generic_proofs)
                   layouts types typ)
          | Module_argument path ->
              let* argument = proof_module path ~at:resource.resource_at in
              resource_dependencies (resource.resource_id :: seen) argument)
      in
      Ok (aliases @ List.concat dependencies)
  in
  let* module_declarations =
    all (runtime_modules @ proof_modules) ~f:(fun member ->
        let* dependencies =
          match
            List.find modules ~f:(fun (_, candidate) -> phys_equal member candidate)
          with
          | Some (source_name, _) ->
              let data =
                List.find_exn data_types ~f:(fun d ->
                    String.equal d.Datatypes.module_name source_name)
              in
              Ok
                (Result_layouts.dependencies
                   ~additional:(Generic_proofs.layout_dependencies generic_proofs)
                   layouts types data)
          | None ->
              let resource_name =
                fst
                  (List.find_exn native_resource_members ~f:(fun (_, candidate) ->
                       phys_equal member candidate))
              in
              let resource =
                List.find_exn source.proof_resources ~f:(fun r ->
                    String.equal r.Source.resource_backend resource_name)
              in
              resource_dependencies [] resource
        in
        Ok (dependencies, [ member ]))
  in
  let* field_declarations =
    all
      (List.filter types ~f:(fun d ->
           (not (Result_layouts.contains layouts d))
           && not (List.mem generic_runtime_types d ~equal:phys_equal)))
      ~f:(fun d ->
        let* fields = Datatypes.fields ~declarations:[ d ] types in
        Ok
          ( Result_layouts.dependencies
              ~additional:(Generic_proofs.layout_dependencies generic_proofs)
              layouts types d,
            fields ))
  in
  let pending_declarations = ref (module_declarations @ field_declarations) in
  let available_layouts = ref [] in
  let take_declarations () =
    let ready, pending =
      List.partition_tf !pending_declarations ~f:(fun (dependencies, _) ->
          List.for_all dependencies ~f:(fun name ->
              List.mem !available_layouts name ~equal:String.equal))
    in
    pending_declarations := pending;
    List.concat_map ready ~f:snd
  in
  let modules = take_declarations () in
  let refs = ref [] in
  let primitives = ref [] in
  let functions =
    Path_bindings.of_list
      (List.concat_map funcs ~f:(fun f ->
           List.map f.paths ~f:(fun path -> (path, proc_name f)))
      @ List.concat_map checked_operations ~f:(fun operation ->
          List.map operation.operation_paths ~f:(fun path ->
              (path, operation.operation_name))))
  in
  let lifted =
    List.filter_map funcs ~f:(fun f ->
        Option.some_if
          ((not (List.is_empty f.prefix))
          || (not (List.is_empty f.captured))
          || Option.is_some f.role)
          (proc_name f, (f.prefix_count, f.captured, f.role)))
  in
  let lifted = with_body_names lifted in
  let origins = ref [] in
  let ocaml_env = source.env in
  (* The predicates' signatures first, for their bodies and the contracts to use. *)
  let* predicates = predicates ~data:types source in
  let* () = check_scoped_resources ~types source inventory scoped_proofs in
  let* applications =
    all scoped_proofs.applications ~f:(fun view ->
        let formal =
          List.find_map (List.rev view.constraints) ~f:(fun constraint_ ->
              List.Assoc.find constraint_.Module_inventory.signature.signature_resources
                view.source.entry.name.pid_str ~equal:String.equal
              |> Option.map ~f:(fun formal -> (constraint_, formal)))
        in
        match (formal, view.source.kind) with
        | Some (constraint_, formal), Predicate _ ->
            let environment =
              Source.annotation_env source formal.Module_inventory.site.environment
            in
            let* raw =
              Proof_bindings.parameter_types environment formal.declaration.pred_params
            in
            let projection =
              Proof_bindings.signature_type_projection Subst.identity view.path
                constraint_.signature
            in
            Ok { view with types = List.map raw ~f:(Subst.type_expr projection) }
        | _ -> Ok view)
  in
  let scoped_proofs = Proof_bindings.with_applications scoped_proofs applications in
  let* scoped_predicates =
    all (List.filter_map scoped_proofs.bindings ~f:scoped_predicate)
      ~f:(fun ((_, p, _, ts) as declaration) ->
        let* _ = predicate_output_count types p ts in
        Ok declaration)
  in
  let* scoped_inputs =
    all scoped_predicates ~f:(fun (_, p, _, ts) ->
        let* outputs = predicate_output_count types p ts in
        Ok (p.pred_name.pid_str, List.length ts - outputs))
  in
  let predicates = predicates @ scoped_predicates in
  (* The abstract predicates of the libraries, by their qualified names, as [Cell.holds],
     whose parameters' types are the library's own where it declares them. *)
  let* library_preds =
    all libraries ~f:(fun (lib : Library_modules.t) ->
        let* environment = Library_modules.environment source lib in
        all
          (List.filter
             (Annotation.of_comments lib.library.interface_comments)
             ~f:(Annotation.predicate_declaration ~interface:true))
          ~f:(fun a ->
            let* p = Annotation.predicate a in
            let* () =
              match p.pred_body with
              | Some _ -> unsupported a.loc "A predicate of a library with a definition"
              | None -> Ok ()
            in
            let* types =
              all p.pred_params ~f:(fun (_, t) ->
                  Source.ocaml_type environment ~at:a.loc t)
            in
            Ok (lib, p, types)))
  in
  let library_preds = List.concat library_preds in
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
                    all declaration.pred_params ~f:(fun (id, pty) ->
                        Source.ocaml_type environment ~at:id.S.pid_loc pty)
                  in
                  let projected = List.map raw ~f:(Subst.type_expr actual_substitution) in
                  let* () =
                    if
                      List.for_all2_exn projected actual.resource_types
                        ~f:(fun expected actual ->
                          Ctype.is_equal binding.site.environment false [ expected ]
                            [ Subst.type_expr binding.parameter_substitution actual ])
                    then Ok ()
                    else
                      error binding.site.item_loc
                        ("The resource declaration " ^ member
                       ^ " has different parameter types")
                  in
                  let* expected_modes =
                    implicit_parameter_count ~kind:"predicate" declaration.pred_params
                  in
                  let* actual_modes =
                    implicit_parameter_count ~kind:"predicate"
                      actual.resource_declaration.pred_params
                  in
                  let* expected_outputs =
                    predicate_output_count view_types declaration raw
                  in
                  let* actual_outputs =
                    predicate_output_count types actual.resource_declaration
                      actual.resource_types
                  in
                  let* () =
                    if
                      Poly.equal expected_modes actual_modes
                      && expected_outputs = actual_outputs
                    then Ok ()
                    else
                      error binding.site.item_loc
                        ("The resource declaration " ^ member
                       ^ " has different implicit parameter modes")
                  in
                  Ok
                    ( formal,
                      {
                        resource_paths =
                          List.map binding.paths ~f:(fun path -> Path.Pdot (path, member));
                        resource_declaration = declaration;
                        resource_backend = actual.resource_backend;
                        resource_types =
                          List.map raw ~f:(Subst.type_expr source_substitution);
                        resource_raw_types = raw;
                      } ))
        in
        let view =
          {
            view_binding = binding;
            view_key =
              fresh
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
          let* lemma_inputs =
            all function_params ~f:(fun (id, ty) ->
                Source.ocaml_type ocaml_env ~at:id.S.pid_loc ty)
          in
          let* output =
            Source.ocaml_type ocaml_env ~at:function_name.pid_loc function_result
          in
          Ok
            ( function_name.pid_str,
              {
                lemma_raven = function_name.pid_str;
                lemma_constant = List.is_empty function_params;
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
  let atomic_predicates signatures =
    List.concat_map signatures ~f:(fun signature ->
        List.map [ "pending"; "committed" ] ~f:(fun method_ ->
            let inputs, _ = Option.value_exn (atomic_inputs signature method_) in
            let key = signature.au_key ^ "." ^ method_ in
            (key, (key, inputs))))
  in
  let context_atomic ?current_procedure scope signatures =
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
          let project =
            if private_operation then Fn.id else fun ty -> rebase (public ty)
          in
          let token =
            if inside au.au_scope then au.au_token else rebase (public au.au_token)
          in
          Some
            {
              signature with
              au_token = token;
              au_inputs = List.map signature.au_private.inputs ~f:project;
              au_result = project signature.au_private.result;
              au_ghost_outputs = List.map signature.au_private.ghost_outputs ~f:project;
              au_implicit = List.map signature.au_private.implicit ~f:project;
            })
  in
  let context_owners at =
    Option.value_map at ~default:[] ~f:(Proof_scopes.owners_at source.proof_scopes)
  in
  let proof_context ?current_procedure ?at scope preds spec_funcs proof_support =
    let owners = context_owners at in
    let atomic_updates =
      context_atomic ?current_procedure scope proof_support.atomic_updates
    in
    let atomic_keys = List.map (atomic_predicates proof_support.atomic_updates) ~f:fst in
    let atomic_preds = atomic_predicates atomic_updates in
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
          | Predicate _ ->
              Some (binding.public_key, (binding.backend, binding.public_types))
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
                List.split_n binding.public_types
                  (List.length declaration.function_params)
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
          (key, (backend, List.map types ~f:project)))
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
          | Predicate _ -> Some (view.key, (view.backend, List.map view.types ~f:project))
          | _ -> None)
    in
    let application_inputs =
      List.filter_map application_views ~f:(fun view ->
          Option.map
            (List.Assoc.find scoped_inputs view.source.backend ~equal:String.equal)
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
      List.map application_preds ~f:(fun (key, (backend, _)) -> (key, backend))
      @ spec_funcs
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
                    Option.value (definition_target binding)
                      ~default:signature.lemma_raven;
                } )))
    in
    ( private_preds @ preds,
      List.filter_map bindings ~f:(fun binding ->
          match binding.kind with
          | Function _ ->
              Some
                ( binding.entry.name.pid_str,
                  Option.value (definition_target binding) ~default:binding.backend )
          | Predicate _ | Lemma _ | Resource _ | Field _ | Atomic _ | State _ | Action _
            ->
              None)
      @ List.map private_functions ~f:(fun (key, signature) ->
          (key, signature.lemma_raven))
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
  in
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
                      all formal.declaration.pred_params ~f:(fun (id, ty) ->
                          Source.ocaml_type environment ~at:id.S.pid_loc ty)
                    in
                    let ts = List.map ts ~f:(Subst.type_expr substitution) in
                    let* outputs = predicate_output_count types formal.declaration ts in
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
                        List.length ts - outputs ))
              in
              Ok resources)
        in
        Ok (context, List.concat resources))
  in
  let module_context context ~projection (preds, spec_funcs, support) =
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
          (key, (target backend, List.map ts ~f:project)))
    in
    let preds =
      List.map parameters ~f:(fun (_, key, ts, _) -> (key, (key, List.map ts ~f:project)))
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
              {
                resource with
                resource_type = project resource.Source.resource_type;
                resource_path = Subst.module_path projection resource.resource_path;
                resource_operations =
                  List.map resource.resource_operations ~f:(fun (name, inputs, output) ->
                      (name, List.map inputs ~f:project, project output));
              });
        ghost_fields =
          List.map support.ghost_fields ~f:(fun field ->
              {
                field with
                field_owner = project field.Source.field_owner;
                field_value = project field.field_value;
                field_resource =
                  Option.map field.field_resource ~f:(Subst.module_path projection);
              });
        atomic_updates =
          List.map support.atomic_updates ~f:(fun signature ->
              {
                signature with
                au_token = project signature.au_token;
                au_inputs = List.map signature.au_inputs ~f:project;
                au_result = project signature.au_result;
                au_ghost_outputs = List.map signature.au_ghost_outputs ~f:project;
                au_implicit = List.map signature.au_implicit ~f:project;
              });
        logical_functions =
          List.map support.logical_functions ~f:(fun (key, signature) ->
              ( key,
                {
                  signature with
                  lemma_raven = target signature.lemma_raven;
                  lemma_inputs = List.map signature.lemma_inputs ~f:project;
                  lemma_outputs = List.map signature.lemma_outputs ~f:project;
                } ));
        predicate_inputs =
          List.map parameters ~f:(fun (_, key, _, inputs) -> (key, inputs))
          @ support.predicate_inputs;
        opaque_predicates =
          List.map parameters ~f:(fun (_, key, _, _) -> key) @ support.opaque_predicates;
      } )
  in
  let proof_context_for ~preds ~spec_funcs ~proof_support name =
    let context = declaration_context name in
    module_context context ~projection:Subst.identity
      (proof_context (declaration_scope name) preds spec_funcs proof_support)
  in
  let* atomic_updates =
    all atomic_operations ~f:(fun (au_source, f) ->
        let preds, spec_funcs, proof_support =
          proof_context ~current_procedure:(proc_name f) ~at:f.loc
            (Proof_bindings.scope_for_location scoped_proofs f.loc)
            preds spec_funcs proof_support
        in
        let preds, spec_funcs, proof_support =
          let context = asset_context au_source.Source.au_scope in
          module_context context ~projection:context.projection
            (preds, spec_funcs, proof_support)
        in
        let ctx =
          spec_context types ~refs ~primitives ~shared:no_shared ~ocaml_env:f.environment
            ~preds ~spec_funcs ~proof_support origins
        in
        let* formals = formals ctx f in
        let* _, _, implicit, _ =
          contract_env ctx ~spec_funcs f formals ~result:"result"
        in
        let signature =
          List.Assoc.find_exn procedure_signatures (proc_name f) ~equal:String.equal
        in
        let au_inputs =
          List.filter_map f.params ~f:(fun p ->
              match p.fp_kind with Tparam_pat pat -> Some pat.pat_type | _ -> None)
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
                    (Generic_proofs.implementation_projection application.source path)
              | None -> Fn.id
              end
        in
        let shape =
          {
            inputs = List.map au_inputs ~f:project;
            result = project f.body.exp_type;
            ghost_outputs =
              List.map signature.procedure_outputs ~f:(fun (_, ty) -> project ty);
            implicit = List.map implicit ~f:(fun (_, _, ty, _) -> project ty);
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
              begin match Proof_bindings.scope_for_location scoped_proofs f.loc with
              | Some scope when List.equal String.equal scope.namespace f.namespace ->
                  scope.owner
              | _ ->
                  List.find_map f.paths ~f:(function
                    | Path.Pdot (owner, _) ->
                        Some (Proof_bindings.canonical_owner scoped_proofs owner)
                    | _ -> None)
              end
        in
        Ok
          {
            au_key = key;
            au_owner = owner;
            au_private = shape;
            au_token = au_source.au_token;
            au_source;
            au_procedure = au_procedure au_source f;
            au_inputs = shape.inputs;
            au_result = shape.result;
            au_ghost_outputs = shape.ghost_outputs;
            au_implicit = shape.implicit;
          })
  in
  let proof_support = { proof_support with atomic_updates } in
  let atomic_predicates = atomic_predicates (context_atomic None atomic_updates) in
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
          let types_of ps =
            all ps ~f:(fun (id, ty) -> Source.ocaml_type ocaml_env ~at:id.S.pid_loc ty)
          in
          let* implicit = implicit_parameter_count ~kind:"lemma" lemma_params in
          let lemma_implicit_count = Option.value implicit ~default:0 in
          let* lemma_inputs = types_of lemma_params in
          let* lemma_outputs = types_of lemma_returns in
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
  (* The views, with their values, and their ghost fields, on the structures. *)
  let views =
    List.filter_map predicates ~f:(fun (_, p, def, types) ->
        match def with
        | View { value } -> Some (p, value, types)
        | Body _ | Direct_invariant _ | Invariant _ -> None)
  in
  let* view_fields =
    all views ~f:(fun ((p : S.predicate), _, param_types) ->
        let at = p.pred_name.pid_loc in
        let structure = List.hd_exn param_types in
        let* anchor =
          match Option.map (anchor types structure) ~f:fst with
          | Some anchor -> Ok anchor
          | None ->
              error at
                "The structure of a view is a reference: an atomic, a ref or a record \
                 with a mutable field"
        in
        let* typ = Datatypes.typ types ~at (List.last_exn param_types) in
        let field =
          Module_context.member
            (declaration_context p.pred_name.pid_str)
            (view_field p.pred_name.pid_str)
        in
        Ok (anchor, (field, typ, None)))
  in
  let resolve_function ~environment (id : S.id) =
    match Source.value_path environment (S.Qid id) with
    | Some path ->
        let path = Proof_bindings.canonical_owner scoped_proofs path in
        begin match
          List.find funcs ~f:(fun f -> List.mem f.paths path ~equal:Path.same)
        with
        | Some f -> Ok f.id
        | None ->
            begin match
              List.find_map generic_proofs ~f:(fun plan ->
                  Generic_proofs.function_id plan path)
            with
            | Some id -> Ok id
            | None ->
                error id.pid_loc
                  (Printf.sprintf "There is no implementation function %s" id.pid_str)
            end
        end
    | None ->
        error id.pid_loc
          (Printf.sprintf "There is no implementation function %s" id.pid_str)
  in
  (* The structures with a state, and their histories, allocated empty. *)
  let action_declarations =
    List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
        match entry.Proof_scopes.declaration with
        | S.Proof_action declaration ->
            let scope = Option.some_if (Option.is_some entry.scope.owner) entry.scope in
            let backend =
              Option.value_map
                (List.find scoped_proofs.bindings ~f:(fun binding ->
                     Ident.same binding.entry.id entry.id))
                ~default:declaration.action_name.pid_str
                ~f:(fun binding -> binding.backend)
            in
            Some
              ( scope,
                Source.annotation_env source entry.scope.environment,
                backend,
                entry.declaration )
        | _ -> None)
  in
  let* actions =
    all action_declarations ~f:(fun (scope, environment, backend, proof) ->
        match proof with
        | S.Proof_action declaration ->
            let* linearizes =
              all declaration.action_linearizes ~f:(resolve_function ~environment)
            in
            let helps =
              Option.bind declaration.action_helps ~f:(fun (field, key, result) ->
                  match field.term_desc with
                  | Tfield (_, Qid field) -> Some (field.pid_str, key, result)
                  | _ -> None)
            in
            Ok
              ( scope,
                {
                  action = backend;
                  params = List.map declaration.action_params ~f:(fun id -> id.S.pid_str);
                  step =
                    Option.map declaration.action_step ~f:(fun (op, args) ->
                        (op.pid_str, args));
                  state = declaration.action_state.pid_str;
                  update =
                    List.map declaration.action_update ~f:(fun (field, term) ->
                        (field.S.pid_str, term));
                  linearizes;
                  helps;
                  action_at = declaration.action_name.pid_loc;
                } )
        | _ -> error Location.none "Expected an action declaration")
  in
  let same_scope a b =
    Option.equal
      (fun a b -> Option.equal Path.same a.Proof_scopes.owner b.Proof_scopes.owner)
      a b
  in
  let* structures =
    all
      (List.filter_map predicates ~f:(fun (at, p, def, param_types) ->
           match def with
           | Invariant { state; fields; body; field_environment; field_scope } ->
               Some
                 (at, p, state, fields, body, param_types, field_environment, field_scope)
           | Body _ | Direct_invariant _ | View _ -> None))
      ~f:(fun
          ( at,
            (p : S.predicate),
            state,
            state_fields,
            body,
            param_types,
            field_environment,
            field_scope )
        ->
        let scope = declaration_scope p.pred_name.pid_str in
        let environment = declaration_environment p.pred_name.pid_str in
        let declaration_predicates, declaration_functions, declaration_support =
          proof_context_for ~preds ~spec_funcs ~proof_support p.pred_name.pid_str
        in
        let context =
          { declaration_predicates; declaration_functions; declaration_support }
        in
        let field_type term =
          let* ty = Source.ocaml_type field_environment ~at term in
          let private_state =
            match (field_scope, scope) with
            | None, _ -> true
            | Some owner, Some caller ->
                Option.is_some
                  (Proof_bindings.drop_prefix owner.namespace caller.namespace)
            | Some _, None -> false
          in
          Ok
            (if private_state then ty
             else
               Proof_bindings.context_type scoped_proofs ~environment
                 (Proof_bindings.public_type scoped_proofs ty))
        in
        let actions =
          List.filter_map actions ~f:(fun (owner, action) ->
              Option.some_if
                (same_scope owner scope
                && String.equal action.state state
                && List.for_all action.update ~f:(fun (field, _) ->
                    List.exists state_fields ~f:(fun sf ->
                        String.equal sf.S.sf_name.pid_str field)))
                action)
        in
        (* The key type of a field of pending calls. *)
        let pending_key t =
          match Datatypes.desc types t with
          | Tconstr (path, [ key ], _) when Path.same path source.pending -> Some key
          | _ -> None
        in
        let* fields =
          all state_fields ~f:(fun (sf : S.state_field) ->
              let* t = field_type sf.sf_type in
              let raven = state ^ "_" ^ sf.sf_name.pid_str in
              match pending_key t with
              | Some _ ->
                  (* The registrations, which only grow. *)
                  Ok
                    ( sf.sf_name.pid_str,
                      raven,
                      R.Type.fin_set ~loc:(loc at) (R.Type.ref ~loc:(loc at)),
                      t,
                      true )
              | None ->
                  let* typ = Datatypes.typ types ~at t in
                  Ok (sf.sf_name.pid_str, raven, typ, t, sf.sf_grows))
        in
        let* pendings =
          all
            (List.filter_map state_fields ~f:(fun (sf : S.state_field) ->
                 match field_type sf.sf_type with
                 | Ok t -> Option.map (pending_key t) ~f:(fun key -> (sf, key))
                 | Error _ -> None))
            ~f:(fun ((sf : S.state_field), key) ->
              let field = sf.sf_name.pid_str in
              let* helped =
                match sf.sf_helps with
                | Some f ->
                    resolve_function ~environment:field_environment
                      (S.mk_id ~loc:sf.sf_name.pid_loc f)
                | None ->
                    error sf.sf_name.pid_loc
                      "A field of pending calls names the function whose calls wait, as \
                       [@helps is_empty]"
              in
              let* helping =
                match
                  List.filter_map actions ~f:(fun a ->
                      match a.helps with
                      | Some (f, k, v) when String.equal f field -> Some (a.state, k, v)
                      | _ -> None)
                with
                | [ helping ] -> Ok helping
                | [] ->
                    error sf.sf_name.pid_loc
                      "No action helps the calls of this field: give one as [helps s.f \
                       on key with result]"
                | _ :: _ :: _ ->
                    unsupported sf.sf_name.pid_loc
                      "Helping the calls of a field by several actions"
              in
              Ok
                {
                  pending_field = field;
                  pending_on = state ^ "_" ^ field ^ "_on";
                  key_type = key;
                  helped;
                  helping;
                })
        in
        let chains =
          List.dedup_and_sort ~compare:String.compare
            (List.filter_map (conjuncts body) ~f:(fun t ->
                 Option.map (chain_of ~state t) ~f:(fun (_, _, field, _) -> field)))
        in
        Ok
          {
            context;
            scope;
            environment;
            invariant = p.pred_name.pid_str;
            backend =
              Module_context.member
                (declaration_context p.pred_name.pid_str)
                p.pred_name.pid_str;
            state;
            fields;
            chains = List.map chains ~f:(fun f -> (f, state ^ "_" ^ f ^ "_index"));
            actions;
            pendings;
            held =
              List.filter_map (conjuncts body) ~f:(fun t ->
                  match spine t [] with
                  | ( { term_desc = Tvar (Qid { pid_str = "own"; _ }); _ },
                      [ location; value ] ) ->
                      begin match spine value [] with
                      | ( { term_desc = Tvar (Qid { pid_str = "([])"; _ }); _ },
                          [
                            {
                              term_desc =
                                Tfield
                                  ( { term_desc = Tvar (Qid { pid_str = x; _ }); _ },
                                    Qid { pid_str = f; _ } );
                              _;
                            };
                            position;
                          ] )
                        when String.equal x state && List.mem chains f ~equal:String.equal
                        ->
                          Some (location, f, position)
                      | _ -> None
                      end
                  | _ -> None);
            params =
              List.zip_exn
                (List.map p.pred_params ~f:(fun (x, _) -> x.S.pid_str))
                (List.take param_types (List.length p.pred_params));
            structure_type = List.hd_exn param_types;
            views =
              List.filter_map views ~f:(fun (view, value, view_types) ->
                  let params = List.drop_last_exn view_types in
                  let state_names =
                    List.filter_map (term_references [] value) ~f:(function
                      | S.Qid id
                        when (not
                                (List.exists view.pred_params ~f:(fun (parameter, _) ->
                                     String.equal parameter.S.pid_str id.pid_str)))
                             && List.exists predicates
                                  ~f:(fun (_, predicate, definition, _) ->
                                    same_scope scope
                                      (declaration_scope predicate.S.pred_name.pid_str)
                                    &&
                                    match definition with
                                    | Invariant { state; _ } ->
                                        String.equal state id.pid_str
                                    | _ -> false) ->
                          Some id.pid_str
                      | Qid _ | Qdot _ -> None)
                  in
                  Option.some_if
                    (same_scope scope (declaration_scope view.pred_name.pid_str)
                    && List.length params = List.length param_types
                    && Ctype.is_equal environment false params param_types
                    && (List.is_empty state_names
                       || List.mem state_names state ~equal:String.equal))
                    (view, value));
            at;
          })
  in
  let* _ =
    all actions ~f:(fun (_, action) ->
        match
          List.filter structures ~f:(fun st ->
              List.exists st.actions ~f:(fun a -> String.equal a.action action.action))
        with
        | [ _ ] -> Ok ()
        | [] -> error action.action_at "No stateful invariant matches this action"
        | _ ->
            error action.action_at
              "Several stateful invariants match this action: use distinct state binders")
  in
  let* _ =
    all views ~f:(fun (view, _, _) ->
        match
          List.filter structures ~f:(fun st ->
              List.exists st.views ~f:(fun (p, _) ->
                  String.equal p.S.pred_name.pid_str view.S.pred_name.pid_str))
        with
        | [ _ ] -> Ok ()
        | [] -> error view.pred_name.pid_loc "No stateful invariant matches this view"
        | _ ->
            error view.pred_name.pid_loc
              "Several stateful invariants match this view: use distinct state binders")
  in
  let* application_identities =
    all generics ~f:(fun group ->
        let* identities =
          all group.Generic_modules.applications ~f:(fun application ->
              let* identity =
                Signature_contract.compiler ~at:application.source.argument.site.item_loc
                  (fun () ->
                    Env.normalize_module_path None source.env application.source.identity)
              in
              Ok (application, identity))
        in
        Ok (group.name, identities))
  in
  let canonical_application group application =
    let identities =
      List.Assoc.find_exn application_identities group.Generic_modules.name
        ~equal:String.equal
    in
    let identity = List.Assoc.find_exn identities application ~equal:phys_equal in
    fst (List.find_exn identities ~f:(fun (_, other) -> Path.same other identity))
  in
  let application_aliases =
    List.concat_map generics ~f:(fun group ->
        List.filter_map group.Generic_modules.applications ~f:(fun application ->
            let canonical = canonical_application group application in
            Option.some_if
              (not (phys_equal canonical application))
              (application.name, canonical.name)))
  in
  let canonical_backend backend =
    Option.value
      (List.find_map application_aliases ~f:(fun (alias, target) ->
           Option.map
             (String.chop_prefix backend ~prefix:(alias ^ "."))
             ~f:(fun suffix -> target ^ "." ^ suffix)))
      ~default:backend
  in
  let declared_structures = structures in
  let* application_structures =
    all
      (List.filter_map scoped_proofs.applications ~f:(fun view ->
           Option.map
             (List.find structures ~f:(fun st ->
                  String.equal st.invariant view.source.backend))
             ~f:(fun st -> (view, st))))
      ~f:(fun (view, st) ->
        let plan = Option.value_exn (proof_worker st.invariant) in
        let project = view.Proof_bindings.project_type in
        let rebase text =
          Option.value_map
            (String.chop_prefix text ~prefix:(plan.group.name ^ "."))
            ~default:text
            ~f:(fun suffix ->
              let prefix = (Qualified_name.of_string view.backend).path in
              canonical_backend (String.concat ~sep:"." (prefix @ [ suffix ])))
        in
        let instance =
          List.find_exn plan.group.applications ~f:(fun instance ->
              String.equal view.backend
                (instance.Generic_modules.name ^ "." ^ view.source.backend))
        in
        let projection =
          Generic_proofs.application_projection source plan instance.source view.path
        in
        let project_path = Subst.module_path projection in
        let project_atomic_source (au : Source.proof_au) =
          {
            au with
            au_scope = Option.map au.au_scope ~f:project_path;
            au_path = project_path au.au_path;
            au_operation_path = project_path au.au_operation_path;
            au_operation_type = project au.au_operation_type;
            au_token = project au.au_token;
            au_token_path = project_path au.au_token_path;
            au_token_paths = List.map au.au_token_paths ~f:project_path;
          }
        in
        let project_lemma signature =
          {
            signature with
            lemma_raven = rebase signature.lemma_raven;
            lemma_inputs = List.map signature.lemma_inputs ~f:project;
            lemma_outputs = List.map signature.lemma_outputs ~f:project;
          }
        in
        let support = st.context.declaration_support in
        let support =
          {
            support with
            runtime_functions =
              Path_bindings.of_list
                (List.map support.runtime_functions.entries ~f:(fun (path, target) ->
                     ( project_path path,
                       Qualified_name.of_string (rebase (Qualified_name.to_string target))
                     )));
            predicate_views =
              Path_bindings.of_list
                (List.map support.predicate_views.entries ~f:(fun (path, key) ->
                     (project_path path, rebase key)));
            public_types = List.map support.public_types ~f:project_path;
            library_paths =
              Path_bindings.of_list
                (List.map support.library_paths.entries ~f:(fun (path, names) ->
                     (project_path path, names)));
            resources =
              List.map support.resources ~f:(fun resource ->
                  {
                    resource with
                    resource_backend = rebase resource.Source.resource_backend;
                    resource_path = project_path resource.resource_path;
                    resource_type = project resource.resource_type;
                    resource_operations =
                      List.map resource.resource_operations
                        ~f:(fun (name, inputs, output) ->
                          (name, List.map inputs ~f:project, project output));
                  });
            ghost_fields =
              List.map support.ghost_fields ~f:(fun field ->
                  {
                    field with
                    field_backend = rebase field.Source.field_backend;
                    field_scope = Option.map field.field_scope ~f:project_path;
                    field_path = project_path field.field_path;
                    field_owner = project field.field_owner;
                    field_value = project field.field_value;
                    field_resource = Option.map field.field_resource ~f:project_path;
                  });
            atomic_updates =
              List.map support.atomic_updates ~f:(fun signature ->
                  {
                    signature with
                    au_owner = Option.map signature.au_owner ~f:project_path;
                    au_private =
                      {
                        inputs = List.map signature.au_private.inputs ~f:project;
                        result = project signature.au_private.result;
                        ghost_outputs =
                          List.map signature.au_private.ghost_outputs ~f:project;
                        implicit = List.map signature.au_private.implicit ~f:project;
                      };
                    au_token = project signature.au_token;
                    au_source = project_atomic_source signature.au_source;
                    au_procedure = rebase signature.au_procedure;
                    au_inputs = List.map signature.au_inputs ~f:project;
                    au_result = project signature.au_result;
                    au_ghost_outputs = List.map signature.au_ghost_outputs ~f:project;
                    au_implicit = List.map signature.au_implicit ~f:project;
                  });
            logical_functions =
              List.map support.logical_functions ~f:(fun (key, signature) ->
                  (key, project_lemma signature));
          }
        in
        let* fields =
          all st.fields ~f:(fun (field, raven, typ, ty, grows) ->
              let ty = project ty in
              let* typ =
                if
                  List.exists st.pendings ~f:(fun pending ->
                      String.equal pending.pending_field field)
                then Ok typ
                else Datatypes.typ types ~at:st.at ty
              in
              Ok (field, raven, typ, ty, grows))
        in
        let views =
          List.filter_map st.views ~f:(fun (predicate, value) ->
              Option.map
                (List.find scoped_proofs.applications ~f:(fun other ->
                     Path.same other.path view.path
                     && String.equal other.source.backend predicate.S.pred_name.pid_str))
                ~f:(fun other ->
                  ( {
                      predicate with
                      pred_name = { predicate.pred_name with pid_str = other.key };
                    },
                    value )))
        in
        let member_id id =
          Option.value_map
            (List.find plan.group.representative.body_members ~f:(fun (_, original) ->
                 Ident.same original id))
            ~default:id
            ~f:(fun (name, _) ->
              Option.value
                (List.Assoc.find instance.source.body_members name ~equal:String.equal)
                ~default:id)
        in
        let application_substitution =
          Generic_proofs.application_substitution plan instance.source
        in
        let environment =
          List.fold (Generic_proofs.source_parameters plan) ~init:view.environment
            ~f:(fun environment parameter ->
              let argument =
                Subst.module_path application_substitution (Path.Pident parameter)
              in
              Env.add_module ~noalias:false parameter Types.Mp_present
                (Types.Mty_alias argument) environment)
        in
        Ok
          {
            st with
            invariant = canonical_backend view.backend;
            backend = canonical_backend view.backend;
            fields;
            views;
            environment;
            context =
              {
                declaration_predicates =
                  List.map st.context.declaration_predicates
                    ~f:(fun (key, (target, tys)) ->
                      (key, (rebase target, List.map tys ~f:project)));
                declaration_functions =
                  List.map st.context.declaration_functions ~f:(fun (key, target) ->
                      (key, rebase target));
                declaration_support = support;
              };
            params = List.map st.params ~f:(fun (key, ty) -> (key, project ty));
            structure_type = project st.structure_type;
            actions =
              List.map st.actions ~f:(fun action ->
                  { action with linearizes = List.map action.linearizes ~f:member_id });
            pendings =
              List.map st.pendings ~f:(fun pending ->
                  {
                    pending with
                    key_type = project pending.key_type;
                    helped = member_id pending.helped;
                  });
          })
  in
  let application_structures =
    List.dedup_and_sort application_structures ~compare:(fun left right ->
        String.compare left.backend right.backend)
  in
  let* structure_member_lists =
    all structures ~f:(fun st ->
        let* members = structure_members types st ~at:st.at in
        Ok (st, members))
  in
  let history_fields =
    List.filter_map structures ~f:(fun st ->
        Option.some_if (has_history st)
          (let l = R.Loc.none in
           let qn m x = qualified_name ~loc:l (m ^ "." ^ x) in
           ( Option.value_map (anchor types st.structure_type) ~default:"" ~f:fst,
             ( member_name st "history",
               R.Type.named ~loc:l (qualified_name ~loc:l (module_name st "history")) [],
               Some
                 (R.Expr.call ~loc:l
                    (qn (module_name st "history") "full")
                    [
                      R.Expr.call ~loc:l
                        (qn (module_name st "states") "set")
                        [ R.Expr.set ~loc:l [] ];
                    ]) ) )))
  in
  let view_fields = view_fields @ history_fields in
  let destination_of_group = function
    | None -> Module_context.Flat
    | Some group -> Module_context.Worker group
  in
  let owner_destination name = (declaration_context name).destination in
  let same_group left right =
    Module_context.same_destination (destination_of_group left)
      (destination_of_group right)
  in
  let visible_state group name =
    match owner_destination name with
    | Module_context.Flat -> true
    | destination ->
        Module_context.same_destination destination (destination_of_group group)
  in
  let field_group field =
    List.find generics ~f:(fun group ->
        String.is_prefix field ~prefix:(group.Generic_modules.name ^ "."))
  in
  let make_shared group =
    let persistent =
      List.filter_map predicates ~f:(fun (at, p, def, _) ->
          match def with
          | (Direct_invariant _ | Invariant _)
            when visible_state group p.pred_name.pid_str ->
              Some
                ( Module_context.member
                    (declaration_context p.pred_name.pid_str)
                    p.pred_name.pid_str,
                  at )
          | _ -> None)
    in
    let selected_views =
      List.filter views ~f:(fun (p, _, _) -> visible_state group p.S.pred_name.pid_str)
    in
    let view_names =
      List.map selected_views ~f:(fun (p, _, _) ->
          let key = p.S.pred_name.pid_str in
          let field = Module_context.member (declaration_context key) (view_field key) in
          (key, field))
    in
    let persistent, view_names =
      match group with
      | Some _ -> (persistent, view_names)
      | None ->
          List.fold scoped_proofs.applications ~init:(persistent, view_names)
            ~f:(fun (persistent, views) view ->
              match view.source.kind with
              | Predicate (p, View _) ->
                  let backend = Qualified_name.of_string view.backend in
                  ( persistent,
                    ( view.key,
                      canonical_backend
                        (String.concat ~sep:"."
                           (backend.path @ [ view_field backend.name ])) )
                    :: views )
              | Predicate (p, _) when p.pred_persistent ->
                  ( (canonical_backend view.backend, p.pred_name.pid_loc) :: persistent,
                    views )
              | _ -> (persistent, views))
    in
    let selected_fields =
      List.filter view_fields ~f:(fun (_, (field, _, _)) ->
          match field_group field with
          | None -> true
          | Some owner -> Option.exists group ~f:(phys_equal owner))
    in
    {
      persistent;
      member_aliases = (if Option.is_none group then application_aliases else []);
      views = view_names;
      structures =
        (List.filter_map declared_structures ~f:(fun st ->
             Option.some_if
               (visible_state group st.invariant)
               { st with invariant = st.backend })
        @ if Option.is_none group then application_structures else []);
      dynamic_indices = false;
      anchors =
        List.map
          (List.dedup_and_sort (List.map selected_fields ~f:fst) ~compare:String.compare)
          ~f:(fun anchor ->
            ( anchor,
              List.filter_map selected_fields ~f:(fun (owner, field) ->
                  Option.some_if (String.equal owner anchor) field) ));
    }
  in
  let shared = make_shared None in
  let generic_shared =
    List.map generics ~f:(fun group ->
        (group.Generic_modules.name, make_shared (Some group)))
  in
  let shared_for_destination = function
    | Module_context.Flat -> shared
    | Module_context.Worker group ->
        List.Assoc.find_exn generic_shared group.Generic_modules.name ~equal:String.equal
  in
  let shared_for_proof name = shared_for_destination (owner_destination name) in
  let body_shared f = shared_for_destination (body_module_context f).destination in
  let state_members group lists =
    List.concat_map lists ~f:(fun (st, members) ->
        Option.some_if
          (Module_context.same_destination
             (owner_destination st.invariant)
             (destination_of_group group))
          members
        |> Option.value ~default:[])
  in
  let past_structures ?(symbolic = false) (f : func) =
    let scope = Proof_bindings.scope_for_location scoped_proofs f.loc in
    let context = proof_context scope preds spec_funcs proof_support in
    let owner = body_module_context f in
    let predicates, _, support =
      module_context owner ~projection:owner.projection context
    in
    let selected_shared = if symbolic then body_shared f else shared in
    let predicates =
      match (symbolic, body_owner f) with
      | false, Some (group, _) ->
          let _, application, _ =
            Option.value_exn (Generic_modules.member generics f.id)
          in
          let target = (canonical_application group application).name in
          List.map predicates ~f:(fun (key, (backend, types)) ->
              let backend =
                Option.value_map
                  (String.chop_prefix backend ~prefix:(group.name ^ "."))
                  ~default:backend
                  ~f:(fun suffix -> target ^ "." ^ suffix)
              in
              (key, (backend, types)))
      | _ -> predicates
    in
    let structures = selected_shared.structures in
    let references =
      Option.value_map f.contract ~default:[] ~f:(fun c ->
          List.concat_map (c.requires @ c.ensures) ~f:(term_references []))
    in
    let keys =
      List.filter_map references ~f:(fun q ->
          let key =
            match (support.proof_key f.environment q, q) with
            | Some key, _ -> Some key
            | None, S.Qid id -> Some id.pid_str
            | None, Qdot _ -> None
          in
          Option.map key ~f:(fun key ->
              Option.value_map (List.Assoc.find predicates key ~equal:String.equal)
                ~default:key ~f:(fun (backend, _) ->
                  canonical_member selected_shared backend)))
    in
    let selected =
      List.filter structures ~f:(fun st ->
          List.mem keys st.invariant ~equal:String.equal
          || List.exists st.views ~f:(fun (p, _) ->
              List.mem keys
                (Option.value_map
                   (List.Assoc.find predicates p.S.pred_name.pid_str ~equal:String.equal)
                   ~default:p.pred_name.pid_str ~f:(fun (backend, _) ->
                     canonical_member selected_shared backend))
                ~equal:String.equal))
    in
    if not (List.is_empty selected) then selected
    else
      let namespace =
        Option.value_map scope ~default:[] ~f:(fun s -> s.Proof_scopes.namespace)
      in
      let owner st =
        Option.value_map st.scope ~default:[] ~f:(fun s -> s.Proof_scopes.namespace)
      in
      let visible =
        List.filter structures ~f:(fun st ->
            Option.is_some (Proof_bindings.drop_prefix (owner st) namespace))
      in
      List.filter visible ~f:(fun st ->
          not
            (List.exists visible ~f:(fun other ->
                 String.equal st.state other.state
                 && List.length (owner other) > List.length (owner st))))
  in
  (* The facts about earlier states in contracts, by the parameter they are about. *)
  let* pasts =
    all funcs ~f:(fun f ->
        let structures = past_structures f in
        let* _ =
          all
            (Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires @ c.ensures))
            ~f:(fun term ->
              if
                List.count structures ~f:(fun st -> Option.is_some (past_of [ st ] term))
                > 1
              then
                error term.term_loc
                  "Several stateful invariants match this past fact: use distinct state \
                   binders"
              else Ok ())
        in
        let clauses select =
          Option.value_map f.contract ~default:[] ~f:select
          |> List.filter_map ~f:(past_of structures)
        in
        let* _, names =
          contract_names f
            (Option.bind f.contract ~f:(fun c -> c.header))
            (List.length f.params)
        in
        let* required =
          all
            (clauses (fun c -> c.requires))
            ~f:(fun p ->
              let position =
                match p.element.term_desc with
                | Tvar (Qid { pid_str = x; _ }) ->
                    List.findi names ~f:(fun _ n -> Option.equal String.equal n (Some x))
                | _ -> None
              in
              match position with
              | Some (i, _) -> Ok (p.inv, p.field, i)
              | None ->
                  unsupported p.element.term_loc
                    "A fact about an earlier state other than of a parameter,")
        in
        Ok
          ( (proc_name f, required),
            ( proc_name f,
              List.map
                (clauses (fun c -> c.ensures))
                ~f:(fun p -> (p.inv, p.field, entry_of_args types f names p.element)) ) ))
  in
  let pasts, past_returns = List.unzip pasts in
  let body_past_name f inv =
    match body_owner f with
    | None -> inv
    | Some (group, _) ->
        let _, application, _ = Option.value_exn (Generic_modules.member generics f.id) in
        let prefix = (canonical_application group application).name in
        Option.value_map
          (String.chop_prefix inv ~prefix:(prefix ^ "."))
          ~default:inv
          ~f:(fun suffix -> group.name ^ "." ^ suffix)
  in
  let with_body_pasts entries project =
    entries
    @ List.filter_map funcs ~f:(fun f ->
        match body_owner f with
        | Some (_, true) ->
            Option.map
              (List.Assoc.find entries (proc_name f) ~equal:String.equal)
              ~f:(fun value -> (body_proc_name f, project f value))
        | _ -> None)
  in
  let pasts =
    with_body_pasts pasts (fun f clauses ->
        List.map clauses ~f:(fun (inv, field, position) ->
            (body_past_name f inv, field, position)))
  in
  let past_returns =
    with_body_pasts past_returns (fun f clauses ->
        List.map clauses ~f:(fun (inv, field, element) ->
            (body_past_name f inv, field, element)))
  in
  (* For each ghost parameter, a parameter that a precondition makes a field of it. *)
  let* ghost_args =
    all funcs ~f:(fun f ->
        let* _, names =
          contract_names f
            (Option.bind f.contract ~f:(fun c -> c.header))
            (List.length f.params)
        in
        let equations =
          field_equations
            (Option.value_map f.contract ~default:[] ~f:(fun c -> c.requires))
        in
        Ok
          ( proc_name f,
            List.map (ghost_params f) ~f:(fun (g, _) ->
                List.find_map equations ~f:(fun (x, field, h) ->
                    if not (String.equal h g.S.pid_str) then None
                    else
                      Option.map
                        (List.findi names ~f:(fun _ n ->
                             Option.equal String.equal n (Some x)))
                        ~f:(fun (i, _) -> (i, field)))) ))
  in
  let ghost_args = with_body_names ghost_args in
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
          data = ctx.types;
          funcs = ctx.spec_funcs;
          vars = [];
          var_types = [];
          logical_definition = false;
        }
      in
      Option.map
        (List.Assoc.find ctx.preds (logical_key env q) ~equal:String.equal)
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
              proc data ~refs ~primitives ~shared:(body_shared f) ~ocaml_env:f.environment
                ~preds:predicates ~funcs:spec_funcs ~annotations ~access_proofs
                ~return_proofs ~initializations ~linearizations ~lifted ~pasts
                ~past_structures:(past_structures ~symbolic:true f)
                ~past_returns ~ghost_args ~procedure_signatures
                ~proof_lemmas:
                  (let context = body_module_context f in
                   module_lemmas context
                     ~project:(Module_context.project_type context)
                     (lemma_context ~at:f.loc (Some context.scope)))
                ~proof_support
                ~predicate_bodies:
                  (let context = body_module_context f in
                   List.map (body_contexts ~at:f.loc (Some context.scope))
                     ~f:(fun (key, body) ->
                       ( key,
                         {
                           body with
                           project_type =
                             (fun typ ->
                               Module_context.project_type context (body.project_type typ));
                         } )))
                ~libraries:(library_paths libraries) functions origins
                ~proc_name:(body_proc_name f) ~pure:(is_pure f) ~declaration_name
                ~primitive_namespace ~pure_name:(body_pure_reference f) f
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
