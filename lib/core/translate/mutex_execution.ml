(** The hidden execution owner and entry holdings of a native procedure. *)

open Base
module R = Raven_api

let variable ~loc text = R.Expr.var ~loc (R.Name.make ~loc text)
let arguments ~loc ~owner ~held = [ variable ~loc owner; variable ~loc held ]

let context ~loc ~owner ~held =
  Mutex_contract.execution_context ~loc (variable ~loc owner) (variable ~loc held)

let formals ~loc ~owner ~held =
  [
    R.Var.make ~loc ~ghost:true (R.Ident.make ~loc owner) (R.Type.ref ~loc);
    R.Var.make ~loc ~ghost:true (R.Ident.make ~loc held)
      (Mutex_contract.held_set_type ~loc);
  ]

let enabled resources =
  List.exists resources ~f:(fun resource ->
      List.equal String.equal resource.Source_core.resource_functor
        [ Mutex_contract.protocol_name ])

let has_context ?trusted environment terms =
  List.exists
    (List.concat_map terms ~f:(Translate_context.term_references []))
    ~f:(Source.is_mutex_context ?trusted environment)

type witness = Owner | Held

(** Implicit names that describe the existing execution context. *)
let entry_bindings ?trusted environment ~implicit contract =
  let open Translate_context in
  let terms = Option.value_map contract ~default:[] ~f:(fun c -> c.S.requires) in
  List.concat_map (List.concat_map terms ~f:conjuncts) ~f:(fun term ->
      match spine term [] with
      | { S.term_desc = Tvar q; _ }, [ owner; held ]
        when Source.is_mutex_context ?trusted environment q ->
          List.filter_map
            [ (owner, Owner); (held, Held) ]
            ~f:(fun (term, kind) ->
              match term.S.term_desc with
              | Tvar (Qid id) when List.mem implicit id.pid_str ~equal:String.equal ->
                  Some (id.pid_str, kind)
              | _ -> None)
      | _ -> [])

(** Outcomes whose omitted context clause preserves the entry holdings. *)
let exit_defaults ?trusted environment ~at ~raising
    (contract : Caravan_spec.Spec_ast.contract option) =
  let open Translate_context in
  let posts = Option.value_map contract ~default:[] ~f:(fun c -> c.ensures) in
  let raises = Option.value_map contract ~default:[] ~f:(fun c -> c.raises) in
  let explicit terms = has_context ?trusted environment terms in
  if
    (not (explicit posts))
    && not (List.exists raises ~f:(fun (_, post) -> explicit (Option.to_list post)))
  then [ None ]
  else
    let guard pattern =
      Some
        (S.mk_term
           (Tmatch
              ( Exceptions.outcome_term ~at,
                [
                  (pattern, S.mk_term Ttrue at);
                  (Exceptions.pattern ~at Pwild, S.mk_term Tfalse at);
                ] ))
           at)
    in
    let normal =
      if explicit posts then []
      else if raising then [ guard (Exceptions.constructor_pattern ~at "None" None) ]
      else [ None ]
    in
    let exceptional =
      if not raising then []
      else
        let some pattern = Exceptions.constructor_pattern ~at "Some" (Some pattern) in
        match raises with
        | [] -> [ guard (some (Exceptions.pattern ~at Pwild)) ]
        | clauses ->
            List.filter_map clauses ~f:(fun (pattern, post) ->
                Option.some_if
                  (not (explicit (Option.to_list post)))
                  (guard (some pattern)))
    in
    normal @ exceptional

let validate_contract ?trusted environment
    (contract : Caravan_spec.Spec_ast.contract option) =
  let open Translate_context in
  let context_count terms =
    List.count
      (List.concat_map terms ~f:(term_references []))
      ~f:(Source.is_mutex_context ?trusted environment)
  in
  let channel terms =
    let clauses = List.concat_map terms ~f:conjuncts in
    let direct =
      List.filter clauses ~f:(fun term ->
          match spine term [] with
          | { S.term_desc = Tvar q; _ }, _ ->
              Source.is_mutex_context ?trusted environment q
          | _ -> false)
    in
    match direct with
    | _ :: duplicate :: _ ->
        error duplicate.term_loc
          "An exit or precondition has at most one mutex context clause"
    | _ when context_count terms <> List.length direct ->
        let at =
          Option.value_map (List.hd terms) ~default:Location.none ~f:(fun term ->
              term.S.term_loc)
        in
        error at "A mutex context must be a direct contract conjunct"
    | _ -> Ok ()
  in
  match contract with
  | None -> Ok ()
  | Some contract ->
      let atomic =
        contract.atomic_requires @ contract.atomic_ensures
        @ List.map contract.atomic_raises ~f:snd
      in
      if context_count atomic > 0 then
        error (List.hd_exn atomic).term_loc
          "A mutex context belongs in ordinary contract clauses"
      else
        List.fold_result
          (contract.requires :: contract.ensures
          :: List.map contract.raises ~f:(fun (_, term) -> Option.to_list term))
          ~init:()
          ~f:(fun () terms -> channel terms)

type boundary = {
  formals : R.Var.t list;
  arguments : R.Expr.t list;
  resources : R.Expr.t list;
}

let prepare_boundary (ctx : Translate_context.context) ~at contract =
  let open Translate_context in
  let open State.Syntax in
  let* () =
    State.of_result
      (validate_contract ?trusted:ctx.given.proof_support.execution_context_path
         ctx.given.env contract)
  in
  if not ctx.given.mutex_execution then
    State.return (ctx, { formals = []; arguments = []; resources = [] })
  else
    let l = loc at in
    let* owner = State.fresh "caravan$execution_self" in
    let* held = State.fresh "caravan$execution_entry_held" in
    let ctx =
      {
        ctx with
        given =
          {
            ctx.given with
            execution_owner = Some (variable ~loc:l owner);
            execution_entry_held = Some (variable ~loc:l held);
          };
      }
    in
    State.return
      ( ctx,
        {
          formals = formals ~loc:l ~owner ~held;
          arguments = arguments ~loc:l ~owner ~held;
          resources = [ context ~loc:l ~owner ~held ];
        } )

let entry_environment (env : Translate_context.env) =
  {
    env with
    ctx = { env.ctx with given = { env.ctx.given with execution_contract = true } };
  }

let exit_resources (env : Translate_context.env) (boundary : boundary) ~at ~raising
    contract =
  let open Translate_context in
  let open State.Syntax in
  if List.is_empty boundary.resources then State.return []
  else
    let l = loc at in
    let+ conditions =
      State.all
        (exit_defaults ?trusted:env.ctx.given.proof_support.execution_context_path
           env.ctx.given.env ~at ~raising contract) ~f:(function
        | None -> State.return None
        | Some term -> State.map (Spec_terms.formula env term) ~f:Option.some)
    in
    match conditions with
    | [] -> []
    | _ ->
        let condition =
          if List.exists conditions ~f:Option.is_none then None
          else List.reduce (List.filter_opt conditions) ~f:(R.Expr.binary ~loc:l Or)
        in
        List.map boundary.resources ~f:(fun context ->
            match condition with
            | None -> context
            | Some condition -> R.Expr.binary ~loc:l Impl condition context)

let call_arguments ~at (boundary : boundary) =
  match boundary.arguments with
  | [] -> Translate_context.State.return ([], [])
  | owner :: _ -> Translate_context.State.execution_arguments_for ~at owner

let protocol ~at ~environment resources =
  let open Translate_context in
  let protocols =
    List.filter resources ~f:(fun resource ->
        List.equal String.equal resource.Source.resource_functor
          [ Mutex_contract.protocol_name ])
  in
  let local =
    List.filter protocols ~f:(fun resource ->
        Option.exists
          (Source.module_path environment
             (S.Qid (S.mk_id ~loc:at resource.Source.resource_name)))
          ~f:(Source.resource_has_path resource))
  in
  let protocols = if List.is_empty local then protocols else local in
  let rec canonical seen resource =
    if List.mem seen resource.Source.resource_id ~equal:Ident.same then resource
    else
      match resource.resource_alias_of with
      | None -> resource
      | Some path ->
          begin match Generic_assets.find_resource protocols path with
          | None -> resource
          | Some target -> canonical (resource.resource_id :: seen) target
          end
  in
  let protocols =
    List.map protocols ~f:(canonical [])
    |> List.dedup_and_sort ~compare:(fun a b ->
        String.compare a.Source.resource_backend b.resource_backend)
  in
  match protocols with
  | [ protocol ] when List.is_empty protocol.resource_parameters -> Ok protocol
  | [ _ ] -> unsupported at "A polymorphic native Mutex facade"
  | [] -> error at "Native Mutex access requires a Ghost.Mutex facade"
  | _ -> error at "The native Mutex facade is ambiguous"
