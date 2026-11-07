(** Lexical task selection; ownership remains a verification obligation. *)

open Base
open Translate_context

let ( let+ ) value f = Result.map value ~f

type function_ = {
  paths : Path.t list;
  parameters : (string * Ident.t) list;
  result : string;
  contract : S.contract option;
  environment : Env.t;
  body : Typedtree.expression;
  logical : Translate_context.env;
  scheme : Polymorphic_functions.scheme;
}

type provenance = Unknown | Task of domain_task | Tuple of provenance list

let key (expression : Typedtree.expression) =
  (expression.exp_loc.loc_start.pos_cnum, expression.exp_loc.loc_end.pos_cnum)

let operation = Domain_primitives.operation

let normalized (expression : Typedtree.expression) path =
  Source.normalize_value_path expression.exp_env ~at:expression.exp_loc path

let same left right =
  let rec equal left right =
    match (left, right) with
    | Task left, Task right ->
        String.equal left.domain_key right.domain_key
        && List.equal Polymorphic_functions.same_type left.domain_arguments
             right.domain_arguments
    | Tuple left, Tuple right -> List.equal equal left right
    | Unknown, Unknown -> true
    | (Task _ | Tuple _ | Unknown), _ -> false
  in
  if equal left right then left else Unknown

let resource_task ~canonical ~tasks environment head =
  match head.S.term_desc with
  | Tvar (Qdot (owner, method_)) when String.equal method_.pid_str "handle" ->
      Option.bind (Source.module_path environment owner) ~f:(fun path ->
          List.find tasks ~f:(fun task ->
              List.exists task.domain_handle_paths ~f:(fun handle_path ->
                  Path.same
                    (canonical (Path.Pdot (path, "handle")))
                    (canonical handle_path))))
  | _ -> None

let specialize ~types ~environment ~at task actuals =
  let actuals = List.map actuals ~f:(Option.map ~f:(Datatypes.quantified_type types)) in
  if List.is_empty task.domain_worker.variables then Ok task
  else
    let* arguments =
      Generic_parameters.instantiate ~environment ~opaque:(Datatypes.is_opaque types)
        ~expand:(Datatypes.expand types) ~at task.domain_worker actuals
      |> Result.map_error ~f:(fun _ ->
          Report.error Type at
            "Cannot infer consistent task type parameters from the handle and captured \
             arguments")
    in
    let* substitute =
      Report.expect ~at "The task's type arguments"
        (Datatypes.substitution task.domain_worker.variables arguments)
    in
    Ok
      {
        task with
        domain_arguments = arguments;
        domain_inputs = List.map task.domain_inputs ~f:substitute;
        domain_result = substitute task.domain_result;
      }

let resource_names ~canonical ~types ~tasks function_ terms =
  all (List.concat_map terms ~f:conjuncts) ~f:(fun term ->
      let head, arguments = spine (S.chain term) [] in
      match (resource_task ~canonical ~tasks function_.environment head, arguments) with
      | Some task, { term_desc = Tvar (Qid name); _ } :: _ ->
          let+ task =
            specialize
              ~types:(function_.logical.data @ types)
              ~environment:function_.environment ~at:term.term_loc task
              (List.map arguments ~f:(Spec_terms.term_type function_.logical))
          in
          Some (name.pid_str, task)
      | _ -> Ok None)
  |> Result.map ~f:List.filter_opt

let returned_task ~canonical ~types ~tasks function_ =
  let* resources =
    resource_names ~canonical ~types ~tasks function_
      (Option.value_map function_.contract ~default:[] ~f:(fun contract ->
           contract.ensures))
  in
  Ok
    (match
       List.filter_map resources ~f:(fun (name, key) ->
           Option.some_if (String.equal name function_.result) (Task key))
     with
    | [] -> Unknown
    | first :: rest -> List.fold rest ~init:first ~f:same)

let rec bind_pattern bindings (pattern : Typedtree.pattern) provenance =
  match (pattern.pat_desc, provenance) with
  | Tpat_var (id, _, _), _ -> List.Assoc.add bindings id provenance ~equal:Ident.same
  | Tpat_alias (pattern, id, _, _, _), _ ->
      bind_pattern
        (List.Assoc.add bindings id provenance ~equal:Ident.same)
        pattern provenance
  | Tpat_tuple fields, Tuple values when List.length fields = List.length values ->
      List.fold2_exn fields values ~init:bindings ~f:(fun bindings (_, pattern) value ->
          bind_pattern bindings pattern value)
  | _ -> bindings

let captured_value unit_ids (expression : Typedtree.expression) =
  match expression.exp_desc with
  | Texp_ident (Pident id, _, _) when List.mem unit_ids id ~equal:Ident.same ->
      Some Unit_argument
  | Texp_ident _ | Texp_constant _ | Texp_construct (_, _, []) ->
      Some (Value_argument expression)
  | _ -> None

let task_for_path ~tasks expression path =
  let* path = normalized expression path in
  match
    List.filter tasks ~f:(fun task -> List.mem task.domain_paths path ~equal:Path.same)
  with
  | [ task ] -> Ok task
  | [] ->
      error expression.exp_loc
        "Domain.spawn requires a Ghost.Task facade for its operation"
  | _ ->
      error expression.exp_loc
        "Domain.spawn has more than one task facade for this operation"

let spawn ~types ~tasks (callback : Typedtree.expression) =
  let instantiate task result arguments =
    let* handle =
      Report.expect ~at:callback.exp_loc "The task handle signature"
        (List.hd task.domain_worker.parameters)
    in
    let* handle =
      match Types.get_desc handle with
      | Tconstr (path, _, _) -> Ok (Ctype.newconstr path [ result ])
      | _ -> error callback.exp_loc "The task handle must have type Domain.t"
    in
    specialize ~types ~environment:callback.exp_env ~at:callback.exp_loc task
      (Some handle :: arguments)
  in
  match callback.exp_desc with
  | Texp_ident (path, _, _) ->
      let* task = task_for_path ~tasks callback path in
      let _, result = Proof_types.function_arguments callback.exp_type in
      let* task = instantiate task result [ Some Predef.type_unit ] in
      if
        List.length task.domain_inputs = 1
        && Ctype.is_equal callback.exp_env true task.domain_inputs [ Predef.type_unit ]
      then Ok (task, [ Unit_argument ])
      else
        unsupported callback.exp_loc "A domain task value with parameters other than unit"
  | Texp_function ([ parameter ], Tfunction_body body) ->
      let unit_ids =
        match parameter.fp_kind with
        | Tparam_pat { pat_desc = Tpat_var (id, _, _); _ } -> [ id ]
        | _ -> []
      in
      begin match body.exp_desc with
      | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, arguments) ->
          let* task = task_for_path ~tasks body path in
          let* arguments = plain_args ~at:body.exp_loc arguments in
          let* task =
            instantiate task body.exp_type
              (List.map arguments ~f:(fun argument -> Some argument.Typedtree.exp_type))
          in
          let* values =
            all arguments ~f:(fun argument ->
                match captured_value unit_ids argument with
                | Some value -> Ok value
                | None ->
                    unsupported argument.exp_loc
                      "A domain task argument computed inside its closure; move the \
                       computation into the verified task")
          in
          if List.length values = List.length task.domain_inputs then Ok (task, values)
          else unsupported body.exp_loc "A partially applied domain task"
      | _ -> unsupported body.exp_loc "A domain closure other than a call of a known task"
      end
  | _ -> unsupported callback.exp_loc "A dynamically selected domain task"

let analyze ~canonical ~types ~tasks ~functions function_ =
  let types = function_.logical.data @ types in
  let* resources =
    resource_names ~canonical ~types ~tasks function_
      (Option.value_map function_.contract ~default:[] ~f:(fun contract ->
           contract.requires))
  in
  let bindings =
    List.fold function_.parameters ~init:[] ~f:(fun bindings (name, id) ->
        let candidates =
          List.filter_map resources ~f:(fun (other, key) ->
              Option.some_if (String.equal other name) (Task key))
        in
        match candidates with
        | [] -> bindings
        | first :: rest ->
            List.Assoc.add bindings id
              (List.fold rest ~init:first ~f:same)
              ~equal:Ident.same)
  in
  let select expression handle provenance =
    let candidates =
      match provenance with
      | Task task -> [ task ]
      | Unknown | Tuple _ ->
          List.filter_map tasks ~f:(fun task ->
              if
                List.is_empty task.domain_worker.variables
                && not
                     (Polymorphic_functions.same_type ~expand:(Datatypes.expand types)
                        task.domain_result expression.Typedtree.exp_type)
              then None
              else
                Result.ok
                  (specialize ~types ~environment:expression.Typedtree.exp_env
                     ~at:expression.exp_loc task
                     [ Some handle.Typedtree.exp_type ]))
    in
    match candidates with
    | [ task ] -> Ok task
    | [] ->
        error expression.exp_loc "Domain.join has no known task contract for this handle"
    | _ ->
        error expression.exp_loc
          "Domain.join cannot select a unique task contract for this handle"
  in
  let rec inspect bindings (expression : Typedtree.expression) =
    match expression.exp_desc with
    | Texp_ident (Pident id, _, _) ->
        Ok
          ( [],
            Option.value (List.Assoc.find bindings id ~equal:Ident.same) ~default:Unknown
          )
    | Texp_let (_, value_bindings, body) ->
        let* evaluated =
          all value_bindings ~f:(fun binding ->
              let+ calls, value = inspect bindings binding.Typedtree.vb_expr in
              (binding, calls, value))
        in
        let bindings =
          List.fold evaluated ~init:bindings ~f:(fun bindings (binding, _, value) ->
              bind_pattern bindings binding.Typedtree.vb_pat value)
        in
        let+ calls, value = inspect bindings body in
        (List.concat_map evaluated ~f:(fun (_, calls, _) -> calls) @ calls, value)
    | Texp_apply (({ exp_desc = Texp_ident (path, _, _); _ } as callee), arguments) ->
        let* path = normalized expression path in
        let* arguments = plain_args ~at:expression.exp_loc arguments in
        begin match (operation path, arguments) with
        | Some Spawn, [ callback ] ->
            let+ task, arguments = spawn ~types ~tasks callback in
            ([ (key expression, Domain_fork (task, arguments)) ], Task task)
        | Some Join, [ handle ] ->
            let* calls, provenance = inspect bindings handle in
            let* task = select expression handle provenance in
            Ok (calls @ [ (key expression, Domain_join (task, handle)) ], Unknown)
        | Some _, _ -> unsupported expression.exp_loc "This Domain operation's arguments"
        | None, _ ->
            let* arguments = all arguments ~f:(inspect bindings) in
            let* value =
              match
                List.find functions ~f:(fun function_ ->
                    List.mem function_.paths path ~equal:Path.same)
              with
              | None -> Ok Unknown
              | Some function_ ->
                  let* value = returned_task ~canonical ~types ~tasks function_ in
                  if match value with Unknown -> true | Task _ | Tuple _ -> false then
                    Ok Unknown
                  else
                    let* arguments =
                      Polymorphic_functions.instantiate ~expand:(Datatypes.expand types)
                        ~at:expression.exp_loc function_.scheme
                        ~declaration:function_.scheme.typ ~occurrence:callee.exp_type
                    in
                    let* substitute =
                      Report.expect ~at:expression.exp_loc "The caller's type arguments"
                        (Datatypes.substitution function_.scheme.variables arguments)
                    in
                    let rec map = function
                      | Unknown -> Ok Unknown
                      | Tuple values ->
                          let+ values = all values ~f:map in
                          Tuple values
                      | Task task ->
                          let arguments = List.map task.domain_arguments ~f:substitute in
                          let target =
                            match path with
                            | Path.Pdot (owner, _) ->
                                List.find tasks ~f:(fun candidate ->
                                    String.equal candidate.domain_template
                                      task.domain_template
                                    && Option.exists candidate.domain_owner
                                         ~f:(fun candidate ->
                                           Path.same (canonical owner)
                                             (canonical candidate)))
                            | _ -> None
                          in
                          begin match target with
                          | Some target ->
                              let+ project =
                                Report.expect ~at:expression.exp_loc
                                  "The task application's type arguments"
                                  (Datatypes.substitution target.domain_worker.variables
                                     arguments)
                              in
                              Task
                                {
                                  target with
                                  domain_arguments = arguments;
                                  domain_inputs = List.map target.domain_inputs ~f:project;
                                  domain_result = project target.domain_result;
                                }
                          | None ->
                              Ok
                                (Task
                                   {
                                     task with
                                     domain_arguments =
                                       List.map task.domain_arguments ~f:substitute;
                                     domain_inputs =
                                       List.map task.domain_inputs ~f:substitute;
                                     domain_result = substitute task.domain_result;
                                   })
                          end
                    in
                    map value
            in
            Ok (List.concat_map arguments ~f:fst, value)
        end
    | Texp_ifthenelse (condition, yes, no) ->
        let* before, _ = inspect bindings condition in
        let* yes_calls, yes = inspect bindings yes in
        let+ no_calls, no =
          match no with None -> Ok ([], Unknown) | Some no -> inspect bindings no
        in
        (before @ yes_calls @ no_calls, same yes no)
    | Texp_tuple fields ->
        let+ fields = all fields ~f:(fun (_, field) -> inspect bindings field) in
        (List.concat_map fields ~f:fst, Tuple (List.map fields ~f:snd))
    | Texp_sequence (before, after) ->
        let* before, _ = inspect bindings before in
        let+ after, value = inspect bindings after in
        (before @ after, value)
    | Texp_function _ -> Ok ([], Unknown)
    | _ ->
        let children = ref [] in
        let expr _ child = children := child :: !children in
        let iterator = { Tast_iterator.default_iterator with expr } in
        Tast_iterator.default_iterator.expr iterator expression;
        let+ children = all (List.rev !children) ~f:(inspect bindings) in
        (List.concat_map children ~f:fst, Unknown)
  in
  Result.map (inspect bindings function_.body) ~f:fst

let application_raises calls expression =
  match List.Assoc.find calls (key expression) ~equal:Poly.equal with
  | Some (Domain_join (task, _)) -> Some task.domain_raises
  | Some (Domain_fork _) | None -> None
