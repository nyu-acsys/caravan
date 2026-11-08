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
  procedure : string;
  native_count : int;
  ghost_inputs : (string * Types.type_expr) list;
  implicit_inputs : (string * Types.type_expr) list;
  ghost_outputs : (string * Types.type_expr) list;
}

let collect ~family_plan ~operation_types ~procedure_name ~given ~resolve ~context
    ~application_view source bindings =
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
      let native_count = List.length operation.params in
      let procedure = procedure_name operation in
      let given = given operation in
      let project = Datatypes.quantified_type (operation_types operation) in
      let native_types =
        List.filter_map operation.params ~f:(fun parameter ->
            match parameter.Typedtree.fp_kind with
            | Tparam_pat pattern -> Some (project pattern.pat_type)
            | Tparam_optional_default _ -> None)
      in
      let* probe =
        Generic_parameters.discover ~key:backend ~name:backend ~at
          ~explicit:(List.length native_types)
          (project operation.body.exp_type :: native_types)
      in
      let given = { given with types = Generic_predicates.types probe given.types } in
      let operation_for_signature =
        {
          operation with
          contract =
            Option.map operation.contract ~f:(fun contract ->
                {
                  contract with
                  requires =
                    List.filter contract.requires ~f:(fun term ->
                        Option.is_none (S.past_membership term));
                  ensures =
                    List.filter contract.ensures ~f:(fun term ->
                        Option.is_none (S.past_membership term));
                });
        }
      in
      let snapshot = Fresh_names.save () in
      let prepared =
        State.run_from State.initial
          (State.in_procedure
             (prepare_proc ~given ~past_structures:[] ~proc_name:procedure
                operation_for_signature))
      in
      Fresh_names.restore snapshot;
      let* prepared, _ = prepared in
      let ghost_inputs =
        List.map prepared.ghosts ~f:(fun (name, _, typ) -> (name, typ))
      in
      let implicit_inputs =
        List.map prepared.implicit ~f:(fun (name, _, typ, _) -> (name, typ))
      in
      let signature =
        List.Assoc.find_exn given.procedure_signatures procedure ~equal:String.equal
      in
      let ghost_outputs = signature.procedure_outputs in
      let handle_types =
        handle_types @ List.map (ghost_inputs @ implicit_inputs) ~f:snd
      in
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
          ~at
          ~explicit:(1 + native_count + List.length ghost_inputs)
          ((Ctype.newconstr domain [ result_type ] :: inputs)
          @ List.map (ghost_inputs @ implicit_inputs) ~f:(fun (_, typ) -> project typ))
      in
      let worker =
        {
          worker with
          member = backend;
          name = Generic_family_plan.proof family_plan backend worker.name;
        }
      in
      let native_arity = 1 + native_count in
      let* native_worker =
        Generic_parameters.discover ~key:backend ~name:worker.name ~at
          ~explicit:native_arity
          (List.take worker.parameters native_arity)
      in
      let* handle_worker =
        Generic_parameters.discover ~key:backend ~name:worker.name ~at
          ~explicit:native_arity
          (List.take handle_types native_arity)
      in
      let* to_handle =
        Report.expect ~at "The task handle's native type parameters"
          (Datatypes.substitution native_worker.variables handle_worker.variables)
      in
      let handle_types =
        List.take handle_types native_arity
        @ List.map (List.drop worker.parameters native_arity) ~f:to_handle
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
        | Some _ -> { worker with parameters = handle_types }
      in
      let ghost_type = match view with None -> project | Some _ -> to_handle in
      let ghost_inputs =
        List.map ghost_inputs ~f:(fun (name, typ) -> (name, ghost_type typ))
      in
      let implicit_inputs =
        List.map implicit_inputs ~f:(fun (name, typ) -> (name, ghost_type typ))
      in
      let ghost_outputs =
        List.map ghost_outputs ~f:(fun (name, typ) -> (name, ghost_type typ))
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
          procedure;
          native_count;
          ghost_inputs;
          implicit_inputs;
          ghost_outputs;
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
    domain_inputs = List.take (List.tl_exn task.worker.parameters) task.native_count;
    domain_result = task.result_type;
    domain_procedure = task.procedure;
    domain_ghost_inputs = task.ghost_inputs;
    domain_implicit_inputs = task.implicit_inputs;
    domain_ghost_outputs = task.ghost_outputs;
    domain_history_inputs =
      List.count contract.requires ~f:(fun term ->
          Option.is_some (S.past_membership term));
    domain_history_outputs =
      List.count contract.ensures ~f:(fun term -> Option.is_some (S.past_membership term));
    domain_capture_hints = [];
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
  let at = task.source.task_at in
  let l = loc at in
  let* prepared = prepare_proc ~given ~past_structures ~proc_name task.operation in
  let f = prepared.func in
  let ctx = prepared.context in
  let contract = Option.value_exn f.contract in
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
  let ghosts = prepared.ghosts in
  let implicits =
    List.map prepared.implicit ~f:(fun (source, raven, typ, _) -> (source, raven, typ))
  in
  let* ghost_types =
    State.all (ghosts @ implicits) ~f:(fun (_, _, typ) -> State.typ ctx ~at typ)
  in
  let* output_types =
    State.all task.ghost_outputs ~f:(fun (_, typ) -> State.typ ctx ~at typ)
  in
  let* () =
    State.iter (f.body.exp_type :: parameter_types) ~f:(State.note_domain given.types)
  in
  let captures = R.Expr.var ~loc:l (name ~loc:l "captures") in
  let output = R.Expr.var ~loc:l (name ~loc:l "ghosts") in
  let capture_count =
    List.length types + List.length ghost_types + (2 * List.length prepared.past_pres)
  in
  let output_count = List.length output_types + (2 * List.length prepared.past_posts) in
  let projection value count index =
    if count = 1 then value else R.Expr.tuple_get ~loc:l value index
  in
  let arguments =
    List.mapi types ~f:(fun index _ -> projection captures capture_count index)
  in
  let ghost_arguments =
    List.mapi ghost_types ~f:(fun index _ ->
        projection captures capture_count (List.length types + index))
  in
  let environment =
    List.fold (List.zip_exn prepared.arg_names arguments)
      ~init:{ prepared.environment with vars = []; logical_definition = false }
      ~f:(fun env (source, value) ->
        Option.value_map source ~default:env ~f:(fun source ->
            bind env source (Value value)))
  in
  let environment =
    List.fold
      (List.zip_exn (ghosts @ implicits) ghost_arguments)
      ~init:environment
      ~f:(fun env ((source, _, _), value) -> bind env source (Value value))
  in
  let environment =
    bind environment prepared.result_name
      (Value
         (if is_unit f.body.exp_type then unit_value ~loc:l
          else R.Expr.var ~loc:l (name ~loc:l "result")))
  in
  let environment =
    List.foldi task.ghost_outputs ~init:environment ~f:(fun index env (source, _) ->
        bind env source (Value (projection output output_count index)))
  in
  let* environment = pattern_definitions environment f in
  let* pre_history =
    history_witness_facts ~ghost:false ctx environment ~at ~requires:contract.requires
      prepared.past_pres
  in
  let* post_history =
    history_witness_facts ~ghost:false ctx environment ~at ~requires:contract.requires
      prepared.past_posts
  in
  let witness_types facts =
    List.concat_map facts ~f:(fun ((_, st, _, _, _), _) ->
        [
          R.Type.named ~loc:l
            (generated_module_member ~loc:l (module_name st "state") "T")
            [];
          R.Type.int ~loc:l;
        ])
  in
  let conjunction = function
    | [] -> R.Expr.bool ~loc:l true
    | terms -> List.reduce_exn terms ~f:(R.Expr.binary ~loc:l And)
  in
  let history_formula facts values =
    let variables = List.concat_map facts ~f:(fun ((_, _, _, decls, _), _) -> decls) in
    let expressions =
      List.concat_map facts ~f:(fun ((_, _, _, _, (snapshot, index)), _) ->
          [ snapshot; index ])
    in
    let equalities = List.map2_exn expressions values ~f:(R.Expr.binary ~loc:l Eq) in
    let body = conjunction (equalities @ List.map facts ~f:snd) in
    if List.is_empty variables then body else R.Expr.exists ~loc:l variables body
  in
  let pre_values =
    List.init
      (2 * List.length pre_history)
      ~f:(fun index ->
        projection captures capture_count
          (List.length types + List.length ghost_types + index))
  in
  let post_values =
    List.init
      (2 * List.length post_history)
      ~f:(fun index -> projection output output_count (List.length output_types + index))
  in
  let* pre = State.all contract.requires ~f:(Spec_terms.formula environment) in
  let pre =
    List.filter_map (List.zip_exn parameter_types arguments) ~f:(fun (typ, value) ->
        Datatypes.admissible ~loc:l given.types typ value)
    @ pre
    @ [ history_formula pre_history pre_values ]
  in
  let* normal = contract_postcondition_formulas environment ~at contract.ensures in
  let normal =
    Option.to_list
      (Datatypes.admissible ~loc:l given.types f.body.exp_type
         (R.Expr.var ~loc:l (name ~loc:l "result")))
    @ normal
    @ [ history_formula post_history post_values ]
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
  let captures_type =
    tuple_type ~loc:l (types @ ghost_types @ witness_types pre_history)
  in
  let outputs_type = tuple_type ~loc:l (output_types @ witness_types post_history) in
  let contract_name = contract_name task in
  let runtime_name = runtime_name task in
  let runtime = Qualified_name.of_string runtime_name in
  let alias_types = types @ ghost_types in
  let alias_values =
    List.mapi alias_types ~f:(fun index _ ->
        R.Expr.var ~loc:l (name ~loc:l ("arg" ^ Int.to_string index)))
  in
  let alias_formals =
    List.mapi alias_types ~f:(fun index typ ->
        R.Var.make ~loc:l ~ghost:(index >= task.native_count)
          (ident ~loc:l ("arg" ^ Int.to_string index))
          typ)
  in
  let alias_formals, alias_implicit =
    List.split_n alias_formals (task.native_count + List.length ghosts)
  in
  let handle = R.Expr.var ~loc:l (name ~loc:l "domain") in
  let stored = Domain_contract.captures ~loc:l ~runtime handle in
  let alias =
    R.Member.callable
      (R.Callable.func ~loc:l ~kind:Pred ~inline:true
         ~formals:
           (R.Var.make ~loc:l (ident ~loc:l "domain") (R.Type.ref ~loc:l) :: alias_formals)
         ~returns:alias_implicit (ident ~loc:l task.backend)
         (Some
            (conjunction
               (Domain_contract.handle ~loc:l ~runtime [ handle; stored ]
               :: List.mapi alias_values ~f:(fun index value ->
                   R.Expr.binary ~loc:l Eq (projection stored capture_count index) value)
               ))))
  in
  let native_values =
    List.map prepared.formals ~f:(fun (source, _, _) ->
        Option.value_map source ~default:(unit_value ~loc:l) ~f:(fun (_, raven) ->
            R.Expr.var ~loc:l (name ~loc:l raven)))
  in
  let proof_values =
    List.map (ghosts @ implicits) ~f:(fun (_, raven, _) ->
        R.Expr.var ~loc:l (name ~loc:l raven))
  in
  let* adapter_history =
    history_witness_facts ctx prepared.environment ~at ~requires:contract.requires
      prepared.past_pres
  in
  let history_values =
    List.concat_map adapter_history ~f:(fun ((_, _, _, _, (snapshot, index)), _) ->
        [ snapshot; index ])
  in
  let capture_value = tuple ~loc:l (native_values @ proof_values @ history_values) in
  let* adapter_pre =
    State.all contract.requires ~f:(Spec_terms.formula prepared.environment)
  in
  let adapter_pre =
    List.filter_map prepared.formals ~f:(fun (_, spec, _) -> spec)
    @ List.map (adapter_pre @ List.map adapter_history ~f:snd) ~f:R.Spec.make
  in
  let* proof_formals =
    State.all ghosts ~f:(fun (_, raven, typ) ->
        let+ typ = State.typ ctx ~at typ in
        R.Var.make ~loc:l ~ghost:true (ident ~loc:l raven) typ)
  in
  let history_formals =
    List.concat_map adapter_history ~f:(fun ((_, _, _, decls, _), _) -> decls)
  in
  let* capture_name = State.fresh "domain_captures" in
  let capture = R.Expr.var ~loc:l (name ~loc:l capture_name) in
  let* handle_name = State.fresh "domain_handle" in
  let result = R.Expr.var ~loc:l (name ~loc:l handle_name) in
  let adapter =
    R.Member.callable
      (R.Callable.proc ~loc:l
         ~formals:
           (List.map prepared.formals ~f:(fun (_, _, v) -> v)
           @ proof_formals @ history_formals
           @ List.map prepared.implicit ~f:(fun (_, _, _, v) -> v))
         ~returns:[ R.Var.make ~loc:l (ident ~loc:l handle_name) (R.Type.ref ~loc:l) ]
         ~requires:adapter_pre
         ~ensures:
           [
             R.Spec.make
               (R.Expr.call ~loc:l (name ~loc:l task.backend)
                  ((result :: native_values) @ proof_values));
             R.Spec.make
               (R.Expr.binary ~loc:l Eq
                  (Domain_contract.captures ~loc:l ~runtime result)
                  capture_value);
           ]
         (ident ~loc:l ("fork$" ^ task.backend))
         (Some
            (R.Stmt.local ~loc:l ~ghost:true ~const:true ~typ:captures_type
               ~init:(R.Stmt.expr_rhs capture_value)
               (ident ~loc:l capture_name)
            @ [
                R.Stmt.fold ~loc:l
                  (qualified_name ~loc:l (contract_name ^ ".precondition"))
                  [ capture ];
              ]
            @ [
                R.Stmt.assign ~loc:l [ result ]
                  (R.Stmt.expr_rhs (Domain_contract.fork ~loc:l ~runtime capture));
                R.Stmt.return ~loc:l [ result ];
              ])))
  in
  let dependencies =
    List.filter_map
      ((f.body.exp_type :: parameter_types)
      @ List.map (ghosts @ implicits) ~f:(fun (_, _, typ) -> typ)
      @ List.map task.ghost_outputs ~f:snd)
      ~f:(Datatypes.dictionary_name given.types)
  in
  State.return
    ( [
        Domain_contract.task_instance ~loc:l ~ghost_results:outputs_type model
          ~name:contract_name ~captures:captures_type ~result:result_type
          ~outcome:outcome_type ~requires:(conjunction pre) ~ensures:post;
        Domain_contract.runtime_instance ~loc:l model ~name:runtime_name
          ~task:(Qualified_name.of_string contract_name);
        alias;
        adapter;
      ],
      dependencies )
