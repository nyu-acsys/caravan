(** Hidden execution resources shared by native procedures and checked calls. *)

open Base
module R = Raven_api

let variable ~loc text = R.Expr.var ~loc (R.Name.make ~loc text)

type boundary = {
  formals : R.Var.t list;
  arguments : R.Expr.t list;
  resources : R.Expr.t list;
  profile : Execution_contract.profile;
}

let empty = { formals = []; arguments = []; resources = []; profile = [] }

let prepare_boundary (ctx : Translate_context.context) ~at contract =
  let open Translate_context in
  let open State.Syntax in
  let* () =
    State.of_result
      (Mutex_execution.validate_contract
         ?trusted:ctx.given.proof_support.execution_context_path ctx.given.env contract)
  in
  let profile = execution_profile ctx.given in
  if not (Execution_contract.enabled profile) then State.return (ctx, empty)
  else
    let l = loc at in
    let* owner_name = State.fresh "caravan$execution_self" in
    let owner = variable ~loc:l owner_name in
    let* held_name =
      if Execution_contract.has_holdings profile then
        State.map (State.fresh "caravan$execution_entry_held") ~f:Option.some
      else State.return None
    in
    let held = Option.map held_name ~f:(variable ~loc:l) in
    let resources =
      Execution_contract.resources ~loc:l profile ~owner
        ~held:(Option.value held ~default:(Execution_contract.empty_held_set ~loc:l))
    in
    let formals =
      R.Var.make ~loc:l ~ghost:true (ident ~loc:l owner_name) (R.Type.ref ~loc:l)
      :: Option.to_list
           (Option.map held_name ~f:(fun held ->
                R.Var.make ~loc:l ~ghost:true (ident ~loc:l held)
                  (Execution_contract.held_set_type ~loc:l)))
    in
    let ctx =
      {
        ctx with
        given =
          { ctx.given with execution_owner = Some owner; execution_entry_held = held };
      }
    in
    State.return
      (ctx, { formals; arguments = owner :: Option.to_list held; resources; profile })

let child_environment ~loc (env : Translate_context.env) owner =
  let profile = Translate_context.execution_profile env.ctx.given in
  if not (Execution_contract.enabled profile) then env
  else
    {
      env with
      ctx =
        {
          env.ctx with
          given =
            {
              env.ctx.given with
              execution_owner = Some owner;
              execution_entry_held =
                Option.some_if
                  (Execution_contract.has_holdings profile)
                  (Execution_contract.empty_held_set ~loc);
              execution_contract = true;
            };
        };
    }

let entry_environment (env : Translate_context.env) =
  {
    env with
    ctx = { env.ctx with given = { env.ctx.given with execution_contract = true } };
  }

let exit_resources (env : Translate_context.env) (boundary : boundary) ~at ~raising
    contract =
  let open Translate_context in
  let open State.Syntax in
  let default_holdings resource =
    let l = loc at in
    let+ conditions =
      State.all
        (Mutex_execution.exit_defaults
           ?trusted:env.ctx.given.proof_support.execution_context_path env.ctx.given.env
           ~at ~raising contract) ~f:(function
        | None -> State.return None
        | Some term -> State.map (Spec_terms.formula env term) ~f:Option.some)
    in
    match conditions with
    | [] -> []
    | _ ->
        if List.exists conditions ~f:Option.is_none then [ resource ]
        else
          let condition =
            List.reduce_exn (List.filter_opt conditions) ~f:(R.Expr.binary ~loc:l Or)
          in
          [ R.Expr.binary ~loc:l Impl condition resource ]
  in
  let+ resources =
    State.all (List.zip_exn boundary.profile boundary.resources)
      ~f:(fun (component, resource) ->
        match component with
        | Execution_contract.Held_locks -> default_holdings resource
        | Visibility -> State.return [ resource ])
  in
  List.concat resources

let call_arguments ~at (boundary : boundary) =
  match boundary.arguments with
  | [] -> Translate_context.State.return ([], [])
  | owner :: _ ->
      Translate_context.State.execution_arguments_for ~at ~profile:boundary.profile owner
