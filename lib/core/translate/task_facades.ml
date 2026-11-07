(** Task contracts and their trusted runtime completion interfaces. *)

open Base
open Translate_context
open Procedures

type t = {
  source : Source.proof_task;
  operation : Procedures.func;
  backend : string;
  key : string;
  handle_types : Types.type_expr list;
  worker : Generic_parameters.t;
  result_type : Types.type_expr;
  emit : bool;
  paths : Path.t list;
}

let collect ~family_plan ~operation_types ~resolve ~context ~application_view source
    bindings =
  all source.Source.proof_tasks ~f:(fun task ->
      let at = task.Source.task_at in
      let view = application_view task in
      let* () =
        if Option.is_some task.task_application && Option.is_none view then
          unsupported at
            "A task facade in a functor application without a shared generic proof body"
        else Ok ()
      in
      let* operation =
        match resolve task with
        | Some operation -> Ok operation
        | None -> unsupported at "A task facade for an imported or unavailable operation"
      in
      let* () =
        match operation.contract with
        | None -> error at "A task facade requires an explicit operation contract"
        | Some contract
          when contract.atomic
               || not
                    (List.is_empty contract.atomic_requires
                    && List.is_empty contract.atomic_ensures
                    && List.is_empty contract.atomic_raises) ->
            unsupported at "A task facade for a logically atomic contract"
        | Some _ -> Ok ()
      in
      let* binding =
        match (view, task.task_scope) with
        | Some view, _ -> Ok (Some view.Proof_bindings.source)
        | None, None -> Ok None
        | None, Some _ ->
            let* binding =
              Report.expect ~at "The scoped task facade"
                (List.find bindings.Proof_bindings.bindings ~f:(fun binding ->
                     match binding.kind with
                     | Task actual -> Ident.same actual.task_id task.task_id
                     | _ -> false))
            in
            Ok (Some binding)
      in
      let backend =
        Option.value_map binding ~default:task.task_name ~f:(fun binding ->
            binding.Proof_bindings.backend)
      in
      let context = context task in
      let* handle =
        match
          match view with
          | Some _ -> Some (Path.Pdot (task.task_path, "handle"))
          | None ->
              Source.value_path task.task_environment
                (S.Qdot (S.Qid (S.mk_id ~loc:at task.task_name), S.mk_id ~loc:at "handle"))
        with
        | None -> error at "The task handle signature is unavailable"
        | Some path ->
            begin try
              let declaration = Env.find_value path task.task_environment in
              Ok declaration.Types.val_type
            with Stdlib.Not_found -> error at "The task handle signature is unavailable"
            end
      in
      let handle_types, _ = Proof_types.function_arguments handle in
      let backend = "task$" ^ backend ^ "$handle" in
      let key =
        Option.value_map view ~default:backend ~f:(fun view ->
            "task$" ^ view.Proof_bindings.key ^ "$handle")
      in
      let project = Datatypes.quantified_type (operation_types operation) in
      let result_type = project operation.body.exp_type in
      let inputs =
        List.filter_map operation.params ~f:(fun parameter ->
            match parameter.Typedtree.fp_kind with
            | Tparam_pat pattern -> Some (project pattern.pat_type)
            | Tparam_optional_default _ -> None)
      in
      let* handle_type =
        Report.expect ~at "The task handle type" (List.hd handle_types)
      in
      let* domain =
        match Types.get_desc handle_type with
        | Tconstr (path, _, _) -> Ok path
        | _ -> error at "The task handle must have type Domain.t"
      in
      let* worker =
        Generic_parameters.discover ~key:backend
          ~name:
            (String.concat ~sep:"."
               (context.Module_context.namespace @ [ "DomainTask$" ^ backend ^ "$Worker" ]))
          ~at ~explicit:(List.length handle_types)
          (Ctype.newconstr domain [ result_type ] :: inputs)
      in
      let worker =
        {
          worker with
          member = backend;
          name = Generic_family_plan.proof family_plan backend worker.name;
        }
      in
      let* worker =
        match view with
        | None -> Ok worker
        | Some view ->
            let* owner =
              Report.expect ~at "The task application's namespace"
                (String.chop_suffix view.backend ~suffix:("." ^ view.source.backend))
            in
            let* worker =
              Generic_parameters.rebind ~expand:Fn.id ~at worker handle_types
            in
            Ok
              {
                worker with
                key;
                name = owner ^ "." ^ (Qualified_name.of_string worker.name).name;
              }
      in
      let result_type, inputs =
        match view with
        | None -> (result_type, inputs)
        | Some _ ->
            let args, result = Proof_types.function_arguments task.task_operation_type in
            (result, args)
      in
      let worker =
        match view with
        | None -> worker
        | Some _ ->
            { worker with parameters = Ctype.newconstr domain [ result_type ] :: inputs }
      in
      let paths =
        match (view, context.worker) with
        | Some _, _ -> [ task.task_operation_path ]
        | None, Some _ -> [ task.task_operation_path; Path.Pident operation.id ]
        | None, None -> operation.paths
      in
      Ok
        {
          source = task;
          operation;
          backend;
          key;
          handle_types;
          worker;
          result_type;
          emit = Option.is_none view;
          paths;
        })

let predicate task = (task.key, (task.worker.name ^ "." ^ task.backend, task.handle_types))

let handle_paths task =
  [
    Path.Pdot (task.source.task_path, "handle");
    Path.Pdot (Path.Pident task.source.task_id, "handle");
  ]

let views task = List.map (handle_paths task) ~f:(fun path -> (path, task.key))
let model = Domain_contract.create ~namespace:[] ~prefix:"Caravan$Domain" ()
let contract_name task = "DomainTask$" ^ task.backend ^ "$Contract"
let runtime_name task = "DomainJoin$" ^ task.backend ^ "$Runtime"

let signature ~types task =
  let contract = Option.value_exn task.operation.contract in
  {
    domain_key = task.key;
    domain_template = task.backend;
    domain_owner =
      (match task.source.task_path with Path.Pdot (owner, _) -> Some owner | _ -> None);
    domain_paths = task.paths;
    domain_handle_paths = handle_paths task;
    domain_worker = task.worker;
    domain_arguments = [];
    domain_runtime = Qualified_name.of_string (runtime_name task);
    domain_contract = Qualified_name.of_string (contract_name task);
    domain_inputs = List.tl_exn task.worker.parameters;
    domain_result = task.result_type;
    domain_raises =
      Exceptions.declared_raises
        ~resolve:(Exceptions.resolver types task.operation.environment)
        contract;
  }

let tuple_type ~loc = function
  | [] -> R.Type.tuple ~loc []
  | [ typ ] -> typ
  | types -> R.Type.tuple ~loc types

let tuple ~loc = function
  | [] -> R.Expr.tuple ~loc []
  | [ value ] -> value
  | values -> R.Expr.tuple ~loc values

let member ~given ~past_structures ~proc_name task =
  State.in_procedure
  @@
  let open State.Syntax in
  let f = task.operation in
  let at = task.source.task_at in
  let l = loc at in
  let* prepared = prepare_proc ~given ~past_structures ~proc_name f in
  let ctx = prepared.context in
  let* () =
    if
      List.is_empty prepared.implicit
      && List.is_empty prepared.ghosts
      && List.is_empty (ghost_results f)
      && List.is_empty prepared.past_pres
      && List.is_empty prepared.past_posts
    then State.return ()
    else
      State.of_result
        (unsupported at
           "A task facade with ghost inputs, ghost results, or history witnesses")
  in
  let* parameter_types =
    State.all f.params ~f:(fun parameter ->
        match parameter.Typedtree.fp_kind with
        | Tparam_pat
            {
              pat_desc = Tpat_var _ | Tpat_any | Tpat_construct (_, _, [], _);
              pat_type;
              _;
            } ->
            State.return pat_type
        | _ ->
            State.of_result
              (unsupported parameter.fp_loc "A destructuring task parameter"))
  in
  let* types = State.all parameter_types ~f:(State.typ ctx ~at) in
  let* () =
    State.iter (f.body.exp_type :: parameter_types) ~f:(State.note_domain given.types)
  in
  let captures_type = tuple_type ~loc:l types in
  let captures = R.Expr.var ~loc:l (name ~loc:l "captures") in
  let arguments =
    List.mapi types ~f:(fun index _ ->
        if List.length types = 1 then captures else R.Expr.tuple_get ~loc:l captures index)
  in
  let parameters = List.zip_exn prepared.arg_names arguments in
  let environment =
    List.fold parameters
      ~init:{ prepared.environment with vars = []; logical_definition = false }
      ~f:(fun env (parameter, value) ->
        Option.value_map parameter ~default:env ~f:(fun parameter ->
            bind env parameter (Value value)))
  in
  let environment =
    bind environment prepared.result_name
      (Value
         (if is_unit f.body.exp_type then R.Expr.tuple ~loc:l []
          else R.Expr.var ~loc:l (name ~loc:l "result")))
  in
  let* environment = pattern_definitions environment f in
  let contract = Option.value_exn f.contract in
  let* pre = State.all contract.requires ~f:(Spec_terms.formula environment) in
  let pre =
    List.filter_map (List.zip_exn parameter_types arguments) ~f:(fun (typ, value) ->
        Datatypes.admissible ~loc:l given.types typ value)
    @ pre
  in
  let* normal = contract_postcondition_formulas environment ~at contract.ensures in
  let normal =
    Option.to_list
      (Datatypes.admissible ~loc:l given.types f.body.exp_type
         (R.Expr.var ~loc:l (name ~loc:l "result")))
    @ normal
  in
  let conjunction = function
    | [] -> R.Expr.bool ~loc:l true
    | expressions -> List.reduce_exn expressions ~f:(R.Expr.binary ~loc:l And)
  in
  let* result_type = State.typ ctx ~at f.body.exp_type in
  let* outcome_type, post =
    if not (raising_contract contract) then
      State.return (R.Type.tuple ~loc:l [], conjunction normal)
    else
      let* outcome_typ = State.typ ctx ~at Translate_context.outcome_type in
      let outcome = R.Expr.var ~loc:l (name ~loc:l "outcome") in
      let environment =
        {
          (bind environment outcome_name (Value outcome)) with
          var_types =
            (outcome_name, Translate_context.outcome_type) :: environment.var_types;
        }
      in
      let set =
        Exceptions.declared_raises
          ~resolve:(Exceptions.resolver given.types f.environment)
          contract
      in
      let clauses =
        Exceptions.raises_postconditions given.types ~at contract.raises set
      in
      let* exceptional = contract_postcondition_formulas environment ~at clauses in
      let normal =
        R.Expr.binary ~loc:l Impl
          (R.Expr.binary ~loc:l Eq outcome (no_exception ~loc:l outcome_typ))
          (conjunction normal)
      in
      State.return (outcome_typ, conjunction (normal :: exceptional))
  in
  let contract_name = contract_name task in
  let runtime_name = runtime_name task in
  let runtime = Qualified_name.of_string runtime_name in
  let formals =
    List.mapi types ~f:(fun index typ ->
        R.Var.make ~loc:l (ident ~loc:l ("arg" ^ Int.to_string index)) typ)
  in
  let actuals =
    List.mapi types ~f:(fun index _ ->
        R.Expr.var ~loc:l (name ~loc:l ("arg" ^ Int.to_string index)))
  in
  let handle = R.Expr.var ~loc:l (name ~loc:l "domain") in
  let alias =
    R.Member.callable
      (R.Callable.func ~loc:l ~kind:Pred ~inline:true
         ~formals:
           (R.Var.make ~loc:l (ident ~loc:l "domain") (R.Type.ref ~loc:l) :: formals)
         (ident ~loc:l task.backend)
         (Some (Domain_contract.handle ~loc:l ~runtime [ handle; tuple ~loc:l actuals ])))
  in
  let dependencies =
    List.filter_map
      (f.body.exp_type :: parameter_types)
      ~f:(Datatypes.dictionary_name given.types)
  in
  State.return
    ( [
        Domain_contract.task_instance ~loc:l model ~name:contract_name
          ~captures:captures_type ~result:result_type ~outcome:outcome_type
          ~requires:(conjunction pre) ~ensures:post;
        Domain_contract.runtime_instance ~loc:l model ~name:runtime_name
          ~task:(Qualified_name.of_string contract_name);
        alias;
      ],
      dependencies )
