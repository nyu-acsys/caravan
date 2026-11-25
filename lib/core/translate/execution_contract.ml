(** The shared hidden execution identity and its independent resource components. *)

open Base
module R = Raven_api

type component = Held_locks | Visibility
type profile = component list

let profile ~mutex ~visibility =
  (if mutex then [ Held_locks ] else []) @ if visibility then [ Visibility ] else []

let enabled profile = not (List.is_empty profile)
let has_holdings profile = List.mem profile Held_locks ~equal:Poly.equal

type context_layout = No_context | Owner | Owner_and_held

let layout profile =
  if has_holdings profile then Owner_and_held
  else if enabled profile then Owner
  else No_context

let context_layout ~mutex ~visibility = layout (profile ~mutex ~visibility)

let context_types ~loc = function
  | No_context -> []
  | Owner -> [ R.Type.ref ~loc ]
  | Owner_and_held -> [ R.Type.ref ~loc; R.Type.fin_set ~loc (R.Type.ref ~loc) ]

let token_context ~loc layout token =
  match context_types ~loc layout with
  | [] -> (token, [])
  | fields ->
      ( R.Expr.tuple_get ~loc token 0,
        List.mapi fields ~f:(fun index _ -> R.Expr.tuple_get ~loc token (index + 1)) )

let module_name = "Caravan$Mutex$Execution"
let interface_name = "Caravan$Mutex$ExecutionSignature"
let execution_name = module_name
let execution_interface = interface_name
let ident ~loc text = R.Ident.make ~loc text
let local ~loc text = R.Name.make ~loc text
let variable ~loc text = R.Expr.var ~loc (local ~loc text)
let held_set_type ~loc = R.Type.fin_set ~loc (R.Type.ref ~loc)
let empty_held_set ~loc = R.Expr.annotated (R.Expr.set ~loc []) (held_set_type ~loc)

let acquired_set ~loc held_set mutex =
  R.Expr.binary ~loc Union held_set (R.Expr.set ~loc [ mutex ])

let released_set ~loc held_set mutex =
  R.Expr.binary ~loc Diff held_set (R.Expr.set ~loc [ mutex ])

let call ~loc text arguments =
  R.Expr.call ~loc (R.Name.make ~loc ~path:[ module_name ] text) arguments

let context ~loc self held_set = call ~loc "context" [ self; held_set ]
let finished ~loc self = call ~loc "finished" [ self ]
let start ~loc = call ~loc "start" []
let finish ~loc self = call ~loc "finish" [ self ]
let start_child ~loc parent = call ~loc "start_child" [ parent ]
let begin_join ~loc parent child = call ~loc "begin_join" [ parent; child ]

let visibility_handoff ~loc source target =
  Visibility_contract.handoff ~loc ~module_name source target

let visibility_transfer ~loc source target lower =
  Visibility_contract.transfer ~loc ~module_name source target lower

let visibility_end_handoff ~loc source target =
  Visibility_contract.end_handoff ~loc ~module_name source target

let snapshot ~loc self = call ~loc "snapshot" [ self ]
let visibility_context ~loc self = Visibility_contract.context ~loc ~module_name self
let captured_types ~loc profile = if enabled profile then [ R.Type.ref ~loc ] else []
let captured_values profile owner = if enabled profile then [ owner ] else []

let initial_arguments ~loc profile owner =
  captured_values profile owner
  @ List.filter_map profile ~f:(function
    | Held_locks -> Some (empty_held_set ~loc)
    | Visibility -> None)

let component_resources profile ~held_locks ~visibility =
  List.map profile ~f:(function Held_locks -> held_locks | Visibility -> visibility)

let resources ~loc profile ~owner ~held =
  component_resources profile ~held_locks:(context ~loc owner held)
    ~visibility:(visibility_context ~loc owner)

let initial_resources ~loc profile owner =
  resources ~loc profile ~owner ~held:(empty_held_set ~loc)

let completion_resources ~loc profile owner =
  if enabled profile then [ finished ~loc owner ] else []

let support ~loc ~mutex ~visibility () =
  let profile = profile ~mutex ~visibility in
  if not (enabled profile) then []
  else
    let self = variable ~loc "self" in
    let held_set = variable ~loc "held_set" in
    let parameter text typ = R.Var.make ~loc ~ghost:true (ident ~loc text) typ in
    let reference text = parameter text (R.Type.ref ~loc) in
    let held_set_parameter ?(implicit = false) text =
      R.Var.make ~loc ~ghost:true ~implicit (ident ~loc text) (held_set_type ~loc)
    in
    let context self held_set =
      R.Expr.call ~loc (local ~loc "context") [ self; held_set ]
    in
    let visibility_context =
      R.Expr.call ~loc (local ~loc "visibility_context") [ self ]
    in
    let initial_resources =
      component_resources profile
        ~held_locks:(context self (empty_held_set ~loc))
        ~visibility:visibility_context
    in
    let finished = R.Expr.call ~loc (local ~loc "finished") [ self ] in
    (* Execution contexts own only ghost state: their predicates depend on no invariant. *)
    let depends body = Option.some_if (Option.is_none body) (loc, []) in
    let declaration text formals body =
      R.Member.callable
        (R.Callable.func ~loc ~kind:Pred ~formals ?depends:(depends body)
           (ident ~loc text) body)
    in
    let context_declaration body =
      R.Member.callable
        (R.Callable.func ~loc ~kind:Pred
           ~formals:[ reference "self" ]
           ~returns:[ held_set_parameter ~implicit:true "held_set" ]
           ?depends:(depends body) (ident ~loc "context") body)
    in
    let start body =
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~returns:[ reference "self" ]
           ~ensures:(List.map initial_resources ~f:R.Spec.make)
           (ident ~loc "start") body)
    in
    let finish body =
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:[ reference "self" ]
           ~requires:(List.map initial_resources ~f:R.Spec.make)
           ~ensures:[ R.Spec.make finished ]
           (ident ~loc "finish") body)
    in
    let snapshot body =
      let current = variable ~loc "current" in
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:[ reference "self"; held_set_parameter ~implicit:true "held_set" ]
           ~returns:[ held_set_parameter "current" ]
           ~requires:[ R.Spec.make (context self held_set) ]
           ~ensures:
             [
               R.Spec.make (context self held_set);
               R.Spec.make (R.Expr.binary ~loc Eq current held_set);
             ]
           (ident ~loc "snapshot") body)
    in
    let exclusive body =
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:
             [ reference "self"; held_set_parameter "first"; held_set_parameter "second" ]
           ~requires:
             [
               R.Spec.make
                 (R.Expr.binary ~loc And
                    (context self (variable ~loc "first"))
                    (context self (variable ~loc "second")));
             ]
           ~ensures:[ R.Spec.make (R.Expr.bool ~loc false) ]
           (ident ~loc "exclusive") body)
    in
    let capability held_set =
      R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Token" ] "excl") [ held_set ]
    in
    let own held_set =
      R.Expr.own ~loc
        [ R.Expr.field ~loc self (local ~loc "execution_token"); capability held_set ]
    in
    let finished_resource =
      List.reduce_exn
        (component_resources profile
           ~held_locks:(own (empty_held_set ~loc))
           ~visibility:visibility_context)
        ~f:(R.Expr.binary ~loc And)
    in
    let initializers =
      (if mutex then
         [ (local ~loc "execution_token", Some (capability (empty_held_set ~loc))) ]
       else [])
      @ if visibility then [ Visibility_contract.initial_field ~loc () ] else []
    in
    let handoff_members ~implementation =
      if not visibility then []
      else
        let parent = variable ~loc "parent" in
        let child = variable ~loc "child" in
        let visibility_context owner =
          R.Expr.call ~loc (local ~loc "visibility_context") [ owner ]
        in
        let handoff source target =
          R.Expr.call ~loc (local ~loc "visibility_handoff") [ source; target ]
        in
        let held = if mutex then [ context child (empty_held_set ~loc) ] else [] in
        let body statements = if implementation then Some statements else None in
        [
          R.Member.callable
            (R.Callable.proc ~loc ~kind:Lemma
               ~formals:[ reference "parent" ]
               ~returns:[ reference "child" ]
               ~requires:[ R.Spec.make (visibility_context parent) ]
               ~ensures:(List.map (handoff parent child :: held) ~f:R.Spec.make)
               (ident ~loc "start_child")
               (body
                  [
                    R.Stmt.assign ~loc [ child ]
                      (R.Stmt.expr_rhs (R.Expr.call ~loc (local ~loc "start") []));
                    R.Stmt.call ~loc (Visibility_contract.begin_handoff ~loc parent child);
                    R.Stmt.return ~loc [ child ];
                  ]));
          R.Member.callable
            (R.Callable.proc ~loc ~kind:Lemma
               ~formals:[ reference "parent"; reference "child" ]
               ~requires:
                 (List.map
                    [
                      visibility_context parent;
                      R.Expr.call ~loc (local ~loc "finished") [ child ];
                    ]
                    ~f:R.Spec.make)
               ~ensures:(List.map (handoff child parent :: held) ~f:R.Spec.make)
               ~opens:(loc, []) (ident ~loc "begin_join")
               (body
                  ([ R.Stmt.unfold ~loc (local ~loc "finished") [ child ] ]
                  @ (if mutex then
                       [
                         R.Stmt.fold ~loc (local ~loc "context")
                           [ child; empty_held_set ~loc ];
                       ]
                     else [])
                  @ [
                      R.Stmt.call ~loc
                        (Visibility_contract.begin_handoff ~loc child parent);
                    ])));
        ]
    in
    let interface_members =
      (if mutex then [ context_declaration None ] else [])
      @ (if visibility then Visibility_contract.interface_members ~loc () else [])
      @ (if visibility then Atomic_visibility_contract.interface_members ~loc () else [])
      @ (if visibility then Frozen_visibility_contract.interface_members ~loc () else [])
      @ handoff_members ~implementation:false
      @ [ declaration "finished" [ reference "self" ] None; start None; finish None ]
      @ if mutex then [ snapshot None; exclusive None ] else []
    in
    let implementation_members =
      (if mutex then
         [
           R.Member.instance ~loc
             ~def:(R.Name.make ~loc ~path:[ "Library" ] "Excl", [ held_set_type ~loc ])
             (ident ~loc "Token")
             (R.Name.make ~loc ~path:[ "Library" ] "Excl");
           R.Member.field ~loc ~ghost:true
             (ident ~loc "execution_token")
             (R.Type.named ~loc (local ~loc "Token") []);
         ]
       else [])
      @ (if visibility then Visibility_contract.implementation_members ~loc () else [])
      @ (if visibility then Atomic_visibility_contract.implementation_members ~loc ()
         else [])
      @ (if visibility then Frozen_visibility_contract.implementation_members ~loc ()
         else [])
      @ (if mutex then [ context_declaration (Some (own held_set)) ] else [])
      @ handoff_members ~implementation:true
      @ [
          declaration "finished" [ reference "self" ] (Some finished_resource);
          start
            (Some
               ([
                  R.Stmt.ghost_block ~loc
                    [ R.Stmt.assign ~loc [ self ] (R.Stmt.new_rhs initializers) ];
                ]
               @ (if mutex then
                    [
                      R.Stmt.fold ~loc (local ~loc "context")
                        [ self; empty_held_set ~loc ];
                    ]
                  else [])
               @ (if visibility then [ Visibility_contract.fold_initial ~loc self ]
                  else [])
               @ [ R.Stmt.return ~loc [ self ] ]));
          finish
            (Some
               ((if mutex then
                   [
                     R.Stmt.unfold ~loc (local ~loc "context")
                       [ self; empty_held_set ~loc ];
                   ]
                 else [])
               @ [ R.Stmt.fold ~loc (local ~loc "finished") [ self ] ]));
        ]
      @
      if mutex then
        [
          snapshot
            (Some
               [
                 R.Stmt.assign ~loc [ variable ~loc "current" ] (R.Stmt.expr_rhs held_set);
               ]);
          exclusive
            (Some
               [
                 R.Stmt.unfold ~loc (local ~loc "context") [ self; variable ~loc "first" ];
                 R.Stmt.unfold ~loc (local ~loc "context")
                   [ self; variable ~loc "second" ];
                 R.Stmt.assert_ ~loc (R.Spec.make (R.Expr.bool ~loc false));
               ]);
        ]
      else []
    in
    [
      R.Member.module_ ~loc ~interface:true (ident ~loc interface_name) interface_members;
      R.Member.module_ ~loc ~sealed:true
        ~implements:[ (local ~loc interface_name, []) ]
        (ident ~loc module_name) implementation_members;
    ]
