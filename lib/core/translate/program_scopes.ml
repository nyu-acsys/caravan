(** The first phase of a program's translation: annotations, the module inventory, generic
    modules and proofs, module contexts, and scoped proofs. *)

open Base
open Translate_context
open Proof_terms
open Procedures
open Program_items
open Proof_declarations

type t = {
  annotations : Annotation.t list;
  linearizations : (int * Annotation.t) list;
  initializations : ((int * int) * Annotation.t) list;
  source : Source.t;
  implementation : Source.proof_resource -> string option;
  proof_implementation : Source.proof_resource -> string option;
  definition_target : Proof_bindings.binding -> string option;
  inventory : Module_inventory.t;
  definition_member_name : string -> string option;
  libraries : Library_modules.t list;
  funcs : Procedures.func list;
  specialized : Specializations.t list;
      (** The functions over a witness whose calls wait, as universal procedures. *)
  access_proofs : ((int * int) * Annotation.t) list;
  return_proofs : ((int * int) * Annotation.t) list;
  types : Datatypes.t list;
  public_types : Path.t list;
  generics : Generic_modules.t list;
  generic_proofs : Generic_proofs.t list;
  module_contexts : Module_context.registry;
  generic_proof_types : Datatypes.t list;
  scoped_proofs : Proof_bindings.t;
  unapplied_proofs : Proof_bindings.t;
}

let definition_resource ~(source : Source.t) scope =
  Option.bind scope.Proof_scopes.owner ~f:(fun owner ->
      List.find source.proof_resources ~f:(fun resource ->
          resource.resource_definition
          && (Path.same owner resource.resource_path
             || Path.same owner (Path.Pident resource.resource_id))))

let scoped_binding ~(unapplied_proofs : Proof_bindings.t) name =
  List.find unapplied_proofs.bindings ~f:(fun binding ->
      String.equal binding.backend name)

let declaration_scope ~(unapplied_proofs : Proof_bindings.t) name =
  let scoped_binding = scoped_binding ~unapplied_proofs in
  Option.map (scoped_binding name) ~f:(fun binding -> binding.entry.scope)

let declaration_environment ~(source : Source.t) ~(unapplied_proofs : Proof_bindings.t)
    name =
  let scoped_binding = scoped_binding ~unapplied_proofs in
  Option.value_map (scoped_binding name) ~default:source.env ~f:(fun binding ->
      binding.environment)

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

let declaration_context ~(module_contexts : Module_context.registry)
    ~(unapplied_proofs : Proof_bindings.t) name =
  let declaration_scope = declaration_scope ~unapplied_proofs in
  Module_context.for_scope module_contexts (declaration_scope name)

let asset_context ~(module_contexts : Module_context.registry) owner =
  Module_context.for_owner module_contexts owner

let context_for_group ~(module_contexts : Module_context.registry) group =
  Option.value
    (Module_context.for_group module_contexts group)
    ~default:module_contexts.root

let proof_worker ~(module_contexts : Module_context.registry)
    ~(unapplied_proofs : Proof_bindings.t) name =
  let declaration_context = declaration_context ~module_contexts ~unapplied_proofs in
  (declaration_context name).worker

let run (source : Source.t) : (t, error) Result.t =
  let annotations = Source.annotations source in
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
  Fresh_names.reset ();
  Fresh_names.reserve
    [
      Monotone_history.order_interface;
      Monotone_history.algebra;
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
      Prelude.value_interface;
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
  let declarations = declarations ~interface:false (direct_source_comments source) in
  let* declared_predicates = all declarations ~f:Annotation.predicate in
  let reserved =
    reserved @ List.map declared_predicates ~f:(fun p -> p.S.pred_name.pid_str)
  in
  Fresh_names.reserve reserved;
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
                let backend = Fresh_names.fresh resource.resource_backend in
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
                  Fresh_names.fresh
                    (String.concat ~sep:"_" (namespace @ [ resource.resource_name ]))
                in
                {
                  resource with
                  resource_backend = backend;
                  resource_descriptor =
                    Datatypes.with_name resource.resource_descriptor backend;
                  resource_public =
                    Option.map resource.resource_public ~f:(fun public ->
                        let backend = Fresh_names.fresh ("Export_" ^ backend) in
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
                    Fresh_names.fresh
                      (String.uncapitalize
                         (String.concat ~sep:"_" (namespace @ [ field.field_name ])));
                });
      proof_types =
        List.map source.proof_types ~f:(fun data ->
            if List.mem scoped_types data.Datatypes.at ~equal:Poly.equal then
              Datatypes.with_name data (Fresh_names.fresh data.module_name)
            else data);
    }
  in
  let resource_implementations =
    List.filter_map source.proof_resources ~f:(fun resource ->
        Option.some_if
          (resource.Source.resource_definition
          && Option.is_none resource.resource_application)
          ( resource.resource_id,
            Fresh_names.fresh ("Implementation_" ^ resource.resource_backend) ))
  in
  let proof_implementations =
    List.filter_map source.proof_resources ~f:(fun resource ->
        Option.some_if
          (resource.Source.resource_definition
          && Option.is_none resource.resource_application)
          (resource.resource_id, Fresh_names.fresh ("Proofs_" ^ resource.resource_backend)))
  in
  let implementation resource =
    List.Assoc.find resource_implementations resource.Source.resource_id ~equal:Ident.same
  in
  let proof_implementation resource =
    List.Assoc.find proof_implementations resource.Source.resource_id ~equal:Ident.same
  in
  let definition_resource = definition_resource ~source in
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
  Fresh_names.reserve
    (List.map (root_interface_resources source inventory) ~f:(fun (_, resource) ->
         resource.Module_inventory.declaration.pred_name.pid_str));
  let* unapplied_proofs = Proof_bindings.build source inventory in
  let scoped_binding = scoped_binding ~unapplied_proofs in
  let definition_member_name name =
    Option.bind (scoped_binding name) ~f:(fun binding ->
        Option.map (definition_target binding) ~f:(fun _ -> binding.entry.name.pid_str))
  in
  let typed = inventory.structure in
  let* libraries = Library_modules.flatten inventory.library_signatures in

  List.iter libraries ~f:(fun lib ->
      List.iter lib.Library_modules.signature.signature_types ~f:(fun (name, _) ->
          Fresh_names.reserve [ lib.library_name ^ "_" ^ name ]));
  let* types, funcs = items ~libraries source inventory in
  let* lifted = all funcs ~f:(fun f -> local_functions ~source f annotations) in
  let lifted =
    List.map (List.concat lifted) ~f:(fun f ->
        { f with raven_name = Fresh_names.fresh f.raven_name })
  in
  (* The functions whose calls wait to be helped, which pending fields name. *)
  let rec helped declarations =
    List.concat_map declarations ~f:(function
      | S.Proof_state { state_fields; _ } ->
          List.filter_map state_fields ~f:(fun field -> field.sf_helps)
      | Proof_module { module_declarations; _ } -> helped module_declarations
      | _ -> [])
  in
  let helped = helped source.proof in
  let* funcs, specialized = Specializations.run types ~helped (funcs @ lifted) in
  let funcs = inherit_contracts funcs in
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
        let* declarations = Library_modules.abstract_types lib in
        Ok
          (List.map declarations ~f:(fun declaration ->
               let descriptor =
                 Datatypes.library_type ~library:lib.library_name
                   ~library_id:lib.library_id ~at:declaration.Typedtree.typ_loc
                   declaration.typ_name.txt
               in
               let descriptor =
                 {
                   descriptor with
                   parameters =
                     List.map declaration.typ_params ~f:(fun (parameter, _) ->
                         parameter.Typedtree.ctyp_type);
                 }
               in
               Datatypes.with_abstract_domain descriptor |> fun descriptor ->
               Datatypes.with_paths descriptor
                 [ Path.Pdot (lib.library_path, declaration.typ_name.txt) ])))
  in
  let types =
    List.concat library_types @ types @ source.proof_types
    @ List.map specialized ~f:(fun (s : Specializations.t) -> s.result)
  in
  let types =
    Datatypes.compiler_aliases
      ~modules:
        (List.map libraries ~f:(fun library ->
             (library.Library_modules.library_path, source.env)))
      types inventory.structure
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
  let universal =
    List.map specialized ~f:(fun (s : Specializations.t) ->
        (s.original.id, s.universal.id))
  in
  let* generics = generic_modules ~universal source ~types ~functions:funcs inventory in
  let* module_scopes = Module_context.collect_scopes source.proof_scopes in
  let* generic_proofs = Generic_proofs.plan generics module_scopes in
  let module_contexts = Module_context.plan ~scopes:module_scopes generic_proofs in
  let* generic_proof_types =
    all generic_proofs ~f:Generic_proofs.types |> Result.map ~f:List.concat
  in
  let* _ =
    all unapplied_proofs.bindings ~f:(fun binding ->
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
  let* applications =
    Generic_proofs.applications source inventory unapplied_proofs generic_proofs
  in
  let scoped_proofs = Proof_bindings.with_applications unapplied_proofs applications in
  Ok
    {
      annotations;
      linearizations;
      initializations;
      source;
      implementation;
      proof_implementation;
      definition_target;
      inventory;
      definition_member_name;
      libraries;
      funcs;
      specialized;
      access_proofs;
      return_proofs;
      types;
      public_types;
      generics;
      generic_proofs;
      module_contexts;
      generic_proof_types;
      scoped_proofs;
      unapplied_proofs;
    }
