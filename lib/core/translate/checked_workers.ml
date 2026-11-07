(** Dictionary-indexed contracts and adapters for checked module members. *)

open Base
open Translate_context
open Procedures
open Program_items

let operation_context ~abstract ~primitive_namespace operation ctx =
  match operation.operation_worker with
  | None -> ctx
  | Some worker ->
      let namespace =
        if List.is_empty primitive_namespace then String.split worker.name ~on:'.'
        else
          primitive_namespace
          @ [
              ((Qualified_name.of_string worker.name).name
              ^ if abstract then "$Contract" else "");
            ]
      in
      let worker = { worker with name = String.concat ~sep:"." namespace } in
      let types =
        List.mapi worker.scheme.variables ~f:(fun index variable ->
            Datatypes.variable_type ~variable ~owner:namespace
              ~parameter:("A" ^ Int.to_string index)
              ~at:worker.loc)
        @ ctx.given.types
      in
      {
        ctx with
        given =
          {
            ctx.given with
            types;
            primitive_namespace = namespace;
            current_polymorphic = Some worker;
            current_procedure = Some (worker.name ^ "." ^ operation.operation_member);
          };
      }

let worker_support ?(inherited = []) ~namespace ~at () =
  let open State.Syntax in
  let* tables = State.gets (fun (state : State.state) -> state.tables) in
  let requests = tables.domains @ tables.dictionaries in
  let* domains =
    State.of_result
      (Result.all
         (List.map tables.domains ~f:(fun request ->
              Datatypes.domain_members request.domain_types [ request.domain_type ])
         @ List.map tables.dictionaries ~f:(fun request ->
             Datatypes.domain_members ~dictionaries:true request.domain_types
               [ request.domain_type ])))
  in
  let domains = Datatypes.unique_domain_members (List.concat domains) in
  let inherited_namespace namespace =
    List.mem inherited namespace ~equal:(List.equal String.equal)
  in
  let inherited_names =
    List.filter_map domains ~f:(fun (name, _) ->
        let name = Qualified_name.of_string name in
        Option.some_if (inherited_namespace name.path) name.name)
    @ List.filter_map tables.function_instances ~f:(fun instance ->
        Option.some_if
          (inherited_namespace instance.instance_namespace)
          instance.instance_name)
    |> Set.of_list (module String)
  in
  let domains =
    List.filter domains ~f:(fun (name, _) ->
        let name = Qualified_name.of_string name in
        not
          (List.equal String.equal name.path namespace
          && Set.mem inherited_names name.name))
  in
  let instances =
    List.filter tables.function_instances ~f:(fun instance ->
        not
          (List.equal String.equal instance.instance_namespace namespace
          && Set.mem inherited_names instance.instance_name))
  in
  let* support =
    State.of_result
      (Generic_support.order ~namespace ~at ~domains
         ~domain_dependencies:(Generic_support.domain_dependencies requests)
         ~instances)
  in
  let defaults =
    List.filter_map tables.defaults ~f:(fun request ->
        Option.some_if
          (List.equal String.equal request.default_namespace namespace)
          (R.Member.free
             (R.Member.value ~loc:(loc at) ~typ:request.default_type
                (ident ~loc:(loc at) (Qualified_name.of_string request.default_name).name)
                None)))
  in
  State.return
    (support @ defaults
    @ List.map (State.primitives_in tables namespace) ~f:(fun primitive ->
        primitive.State.member))

let resource_worker_name target =
  let target = Qualified_name.of_string target in
  Qualified_name.to_string { target with name = "Poly$" ^ target.name }

let resource_generics ~types ~inputs ~workers predicates =
  List.fold_result predicates ~init:workers ~f:(fun workers (key, (target, parameters)) ->
      match Generic_predicates.find ~target workers target with
      | Some worker ->
          let* worker =
            Generic_parameters.rebind ~expand:(Datatypes.expand types) ~at:worker.loc
              worker parameters
          in
          Ok ({ worker with key } :: workers)
      | None ->
          let explicit =
            Option.value
              (List.Assoc.find inputs key ~equal:String.equal)
              ~default:(List.length parameters)
          in
          let* worker =
            Generic_predicates.discover ~expand:(Datatypes.expand types) ~key
              ~name:(resource_worker_name target) ~at:Location.none ~explicit parameters
          in
          if List.is_empty worker.variables then Ok workers
          else
            Ok ({ worker with member = (Qualified_name.of_string target).name } :: workers))

let enrich_predicates ctx predicates =
  let* generic_predicates =
    resource_generics ~types:ctx.given.types
      ~inputs:ctx.given.proof_support.predicate_inputs
      ~workers:ctx.given.generic_predicates predicates
  in
  Ok { ctx with given = { ctx.given with generic_predicates } }

let operation_module ~abstract ?inherited ctx operation member =
  let open State.Syntax in
  match operation.operation_worker with
  | None -> State.return [ R.Member.callable member ]
  | Some worker ->
      let at = operation.operation_signature.site.item_loc in
      let l = loc at in
      let stem = (Qualified_name.of_string worker.name).name in
      let contract = stem ^ "$Contract" in
      let* support =
        worker_support
          ~inherited:
            (Option.value_map inherited ~default:[] ~f:(fun owner ->
                 [ String.split owner ~on:'.' @ [ contract ] ]))
          ~namespace:ctx.given.primitive_namespace ~at ()
      in
      let params =
        List.mapi worker.scheme.variables ~f:(fun index _ ->
            ( ident ~loc:l ("A" ^ Int.to_string index),
              qualified_name ~loc:l Prelude.value_interface ))
      in
      if abstract then
        State.return
          [
            R.Member.module_ ~loc:l ~interface:true ~params (ident ~loc:l contract)
              (support @ [ R.Member.callable member ]);
            R.Member.instance ~loc:l (ident ~loc:l stem) (qualified_name ~loc:l contract);
          ]
      else
        State.return
          [
            R.Member.module_ ~loc:l ~params
              ~implements:
                (if Option.is_some inherited then [ (qualified_name ~loc:l contract, []) ]
                 else [])
              (ident ~loc:l stem)
              (support @ [ R.Member.callable member ]);
          ]

let actual_operation_context ctx view operation ?native ~declaration ~worker ~target
    actual_ctx =
  let open State.Syntax in
  match operation.operation_worker with
  | None -> State.return (actual_ctx, target, Fn.id)
  | Some _ ->
      let at = operation.operation_signature.site.item_loc in
      let occurrence =
        Subst.type_expr view.view_actual_substitution
          (Subst.type_expr operation.operation_signature.substitution
             operation.operation_signature.declaration.val_val.val_type)
      in
      let all_types = ctx.given.types @ actual_ctx.given.types in
      let expand = Datatypes.expand all_types in
      let* scheme =
        State.of_result (Polymorphic_functions.discover ~expand ~at declaration)
      in
      let* arguments =
        State.of_result
          (Polymorphic_functions.instantiate ~expand ~at scheme ~declaration ~occurrence)
      in
      let* worker_arguments =
        match worker with
        | None -> State.return []
        | Some worker ->
            State.of_result
              (Polymorphic_functions.instantiate_worker ~expand ~at worker ~declaration
                 ~occurrence)
      in
      let variables =
        scheme.variables
        @ Option.value_map worker ~default:[] ~f:(fun worker -> worker.scheme.variables)
      in
      let projected_arguments = arguments @ worker_arguments in
      let given = { ctx.given with types = all_types } in
      let* dictionaries = State.dictionaries_given given ~at projected_arguments in
      let bindings =
        List.map2_exn variables dictionaries ~f:(fun variable dictionary ->
            let dictionary = Qualified_name.of_string dictionary in
            let data =
              Datatypes.variable_type ~variable ~owner:dictionary.path
                ~parameter:dictionary.name ~at
            in
            match (native, Types.get_desc variable) with
            | Some native, Tunivar (Some name) ->
                begin match
                  Env.find_type_by_name (Longident.Lident name) native.body.exp_env
                with
                | Pident id, _ -> { data with id = Some id }
                | _ -> data
                | exception Stdlib.Not_found -> data
                end
            | _ -> data)
      in
      let rec project typ =
        match
          List.findi bindings ~f:(fun _ binding ->
              Option.exists binding.Datatypes.variable ~f:(Types.eq_type typ)
              ||
              match Types.get_desc typ with
              | Tconstr (Pident id, [], _) -> Option.exists binding.id ~f:(Ident.same id)
              | _ -> false)
        with
        | Some (index, _) -> List.nth_exn projected_arguments index
        | None ->
            begin match Types.get_desc typ with
            | Tvar _ | Tunivar _ -> typ
            | desc -> Ctype.newty (Btype.copy_type_desc project desc)
            end
      in
      let actual_ctx =
        {
          actual_ctx with
          given =
            {
              actual_ctx.given with
              types = bindings @ all_types;
              primitive_namespace = ctx.given.primitive_namespace;
            };
        }
      in
      let* target =
        match worker with
        | None -> State.return target
        | Some worker ->
            let+ instance =
              State.value_instance actual_ctx ~at ~target:worker.name
                ~arguments:worker_arguments
            in
            instance ^ "." ^ (Qualified_name.of_string target).name
      in
      State.return (actual_ctx, target, project)
