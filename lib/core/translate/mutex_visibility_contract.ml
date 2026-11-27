(** Owner-indexed protected resources and checked visibility handoff envelopes. *)

open Base
module R = Raven_api
module E = Execution_contract
module M = Mutex_contract

let resource_interface = "Caravan$Mutex$TransferableResource"
let protocol_name = "Caravan$Mutex$VisibilityProtocol"
let ident ~loc text = R.Ident.make ~loc text
let local ~loc text = R.Name.make ~loc text
let variable ~loc text = R.Expr.var ~loc (local ~loc text)

let resource_signature ~loc () =
  let reference text = R.Var.make ~loc ~ghost:true (ident ~loc text) (R.Type.ref ~loc) in
  let r =
    R.Var.make ~loc ~ghost:true (ident ~loc "r") (R.Type.named ~loc (local ~loc "T") [])
  in
  let source = variable ~loc "source" in
  let target = variable ~loc "target" in
  let resource owner =
    R.Expr.call ~loc (local ~loc "resource") [ owner; variable ~loc "r" ]
  in
  let handoff = E.visibility_handoff ~loc source target in
  R.Member.module_ ~loc ~interface:true
    ~implements:[ (R.Name.make ~loc ~path:[ "Library" ] "Type", []) ]
    (ident ~loc resource_interface)
    [
      R.Member.type_ ~loc ~rep:true (ident ~loc "T") None;
      R.Member.callable
        (R.Callable.func ~loc ~kind:Pred
           ~formals:
             [
               R.Var.make ~loc (ident ~loc "self") (R.Type.ref ~loc);
               R.Var.make ~loc (ident ~loc "r") (R.Type.named ~loc (local ~loc "T") []);
             ]
           (ident ~loc "resource") None);
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:[ reference "source"; reference "target"; r ]
           ~requires:[ R.Spec.make (R.Expr.binary ~loc And handoff (resource source)) ]
           ~ensures:[ R.Spec.make (R.Expr.binary ~loc And handoff (resource target)) ]
           (ident ~loc "transfer") None);
    ]

let protocol ~loc () =
  let ref_type = R.Type.ref ~loc in
  let resource_type = R.Type.named ~loc (local ~loc "R") [] in
  let reference ?(ghost = true) ?(implicit = false) text =
    R.Var.make ~loc ~ghost ~implicit (ident ~loc text) ref_type
  in
  let protected_parameter ?(implicit = false) () =
    R.Var.make ~loc ~ghost:true ~implicit (ident ~loc "r") resource_type
  in
  let held_parameter ?(implicit = false) () =
    R.Var.make ~loc ~ghost:true ~implicit (ident ~loc "held_set") (E.held_set_type ~loc)
  in
  let m = variable ~loc "m" in
  let c = variable ~loc "c" in
  let self = variable ~loc "self" in
  let r = variable ~loc "r" in
  let held_set = variable ~loc "held_set" in
  let snapshot = variable ~loc "snapshot" in
  let released = variable ~loc "released" in
  let success = variable ~loc "success" in
  let call text arguments = R.Expr.call ~loc (local ~loc text) arguments in
  let resource owner =
    R.Expr.call ~loc (R.Name.make ~loc ~path:[ "R" ] "resource") [ owner; r ]
  in
  let association = call "is_mutex" [ m; r ] in
  let condition = call "is_condition" [ c; m ] in
  let held = call "held" [ m; self ] in
  let current = E.context ~loc self held_set in
  let visible = E.visibility_context ~loc self in
  let contains = R.Expr.binary ~loc In m held_set in
  let not_held = R.Expr.not_ ~loc contains in
  let acquired = E.context ~loc self (E.acquired_set ~loc held_set m) in
  let unlocked = E.context ~loc self (E.released_set ~loc held_set m) in
  let conjunction expressions =
    List.fold expressions ~init:(R.Expr.bool ~loc true) ~f:(R.Expr.binary ~loc And)
  in
  let procedure ?(kind = R.Callable.Proc) ?(trusted = false) text formals returns requires
      ensures body =
    let member =
      R.Member.callable
        (R.Callable.proc ~loc ~kind ~formals ~returns
           ~requires:(List.map requires ~f:R.Spec.make)
           ~ensures:(List.map ensures ~f:R.Spec.make)
           ~opens:(loc, []) (ident ~loc text) body)
    in
    if trusted then R.Member.free member else member
  in
  let invoke expression = R.Stmt.call ~loc expression in
  let assign target expression =
    R.Stmt.assign ~loc [ target ] (R.Stmt.expr_rhs expression)
  in
  let transfer source target =
    invoke
      (R.Expr.call ~loc (R.Name.make ~loc ~path:[ "R" ] "transfer") [ source; target; r ])
  in
  let release owner =
    [
      assign owner (E.start_child ~loc self);
      transfer self owner;
      invoke (E.visibility_end_handoff ~loc self owner);
      invoke (E.finish ~loc owner);
    ]
  in
  let acquire owner =
    [
      invoke (E.begin_join ~loc self owner);
      transfer owner self;
      invoke (E.visibility_end_handoff ~loc owner self);
      invoke (E.finish ~loc owner);
    ]
  in
  let local_owner text = R.Stmt.local ~loc ~ghost:true ~typ:ref_type (ident ~loc text) in
  let packet owner = [ resource owner; E.finished ~loc owner ] in
  let native_mutex = reference ~ghost:false "m" in
  let native_condition = R.Var.make ~loc (ident ~loc "c") (Condition_contract.typ ~loc) in
  let raw_formals =
    [ native_mutex; reference "self"; protected_parameter (); held_parameter () ]
  in
  let public_formals =
    [
      native_mutex;
      reference "self";
      protected_parameter ~implicit:true ();
      held_parameter ~implicit:true ();
    ]
  in
  let raw_arguments = [ m; self; r; held_set ] in
  let acquired_packet = [ association; not_held; acquired; held ] @ packet snapshot in
  let acquired_resource =
    [ association; not_held; acquired; held; visible; resource self ]
  in
  let invariant text formals returns =
    R.Member.free
      (R.Member.callable
         (R.Callable.func ~loc ~kind:Inv ~formals ~returns (ident ~loc text) None))
  in
  let notification_formals =
    [
      native_condition;
      reference "self";
      reference ~implicit:true "m";
      held_parameter ~implicit:true ();
    ]
  in
  let notification_resources = [ current; visible; condition ] in
  R.Member.module_ ~loc
    ~params:[ (ident ~loc "R", local ~loc resource_interface) ]
    (ident ~loc protocol_name)
    [
      R.Member.type_ ~loc (ident ~loc "T") (Some ref_type);
      invariant "is_mutex" [ native_mutex ] [ protected_parameter ~implicit:true () ];
      invariant "is_condition" [ native_condition ] [ reference ~implicit:true "m" ];
      R.Member.callable
        (R.Callable.func ~loc ~kind:Pred ~inline:true
           ~formals:[ native_mutex; reference "self" ]
           (ident ~loc "held")
           (Some (M.held ~loc m self)));
      procedure ~kind:Lemma ~trusted:true "initialize_condition"
        [ native_condition; reference "m" ]
        []
        [ Condition_contract.fresh ~loc c ]
        [ condition ] None;
      procedure ~kind:Lemma ~trusted:true "store_initialize"
        [ native_mutex; protected_parameter (); reference "snapshot" ]
        []
        (M.fresh ~loc m :: packet snapshot)
        [ association ] None;
      procedure ~trusted:true "store_unlock"
        (raw_formals @ [ reference "snapshot" ])
        []
        ([ current; contains; association; held ] @ packet snapshot)
        [ association; unlocked ] None;
      procedure ~trusted:true "take_lock" raw_formals
        [ reference "snapshot" ]
        [ current; association; not_held ]
        acquired_packet None;
      procedure ~trusted:true "take_try_lock" raw_formals
        [
          R.Var.make ~loc (ident ~loc "success") (R.Type.bool ~loc); reference "snapshot";
        ]
        [ current; association ]
        [ association; R.Expr.ite ~loc success (conjunction acquired_packet) current ]
        None;
      procedure ~trusted:true "store_take_wait"
        ((native_condition :: raw_formals) @ [ reference "released" ])
        [ reference "snapshot" ]
        ([ current; contains; association; condition; held ] @ packet released)
        ([ current; association; condition; held ] @ packet snapshot)
        None;
      procedure ~kind:Lemma "initialize"
        [ native_mutex; reference "self"; protected_parameter () ]
        []
        [ M.fresh ~loc m; visible; resource self ]
        [ association; visible ]
        (Some
           (local_owner "snapshot" @ release snapshot
           @ [ invoke (call "store_initialize" [ m; r; snapshot ]) ]));
      procedure "unlock" public_formals []
        [ current; contains; association; held; visible; resource self ]
        [ association; unlocked; visible ]
        (Some
           (local_owner "snapshot" @ release snapshot
           @ [ invoke (call "store_unlock" (raw_arguments @ [ snapshot ])) ]));
      procedure "lock" public_formals []
        [ current; association; not_held; visible ]
        acquired_resource
        (Some
           (local_owner "snapshot"
           @ [ assign snapshot (call "take_lock" raw_arguments) ]
           @ acquire snapshot));
      procedure "try_lock" public_formals
        [ R.Var.make ~loc (ident ~loc "success") (R.Type.bool ~loc) ]
        [ current; association; visible ]
        [
          association;
          visible;
          R.Expr.ite ~loc success
            (conjunction [ not_held; acquired; held; resource self ])
            current;
        ]
        (Some
           (local_owner "snapshot"
           @ [
               R.Stmt.assign ~loc [ success; snapshot ]
                 (R.Stmt.expr_rhs (call "take_try_lock" raw_arguments));
               R.Stmt.if_ ~loc success (acquire snapshot) [];
               R.Stmt.return ~loc [ success ];
             ]));
      procedure "wait"
        (native_condition :: public_formals)
        []
        [ current; contains; association; condition; held; visible; resource self ]
        [ current; association; condition; held; visible; resource self ]
        (Some
           (local_owner "released" @ local_owner "snapshot" @ release released
           @ [
               assign snapshot
                 (call "store_take_wait" ((c :: raw_arguments) @ [ released ]));
             ]
           @ acquire snapshot));
      procedure ~trusted:true "store_signal" notification_formals []
        notification_resources notification_resources None;
      procedure ~trusted:true "store_broadcast" notification_formals []
        notification_resources notification_resources None;
      procedure "signal" notification_formals [] notification_resources
        notification_resources
        (Some [ invoke (call "store_signal" [ c; self ]) ]);
      procedure "broadcast" notification_formals [] notification_resources
        notification_resources
        (Some [ invoke (call "store_broadcast" [ c; self ]) ]);
    ]

let support ~loc () = [ resource_signature ~loc (); protocol ~loc () ]

let source_signatures () =
  let module C = Checked_signatures in
  let parameter = M.public_parameter in
  let resource =
    M.
      {
        resource_declaration with
        declaration_parameters = [ parameter "self" Owner; parameter "r" Carrier ];
      }
  in
  let transfer : M.public_declaration =
    {
      declaration_name = "transfer";
      declaration_kind = R.Ast.Callable.Lemma;
      declaration_parameters =
        [
          parameter ~ghost:true "source" Owner;
          parameter ~ghost:true "target" Owner;
          parameter ~ghost:true "r" Carrier;
        ];
      declaration_results = [];
    }
  in
  let initialize =
    M.
      {
        initialization_declaration with
        declaration_parameters =
          [
            parameter "m" Native_mutex;
            parameter ~ghost:true "self" Owner;
            parameter ~ghost:true "r" Resource;
          ];
      }
  in
  List.filter_map (M.source_signatures ()) ~f:(fun (signature : C.module_signature) ->
      if List.equal String.equal signature.path [ M.resource_interface ] then
        Some
          {
            signature with
            path = [ resource_interface ];
            required_members = [ ("predicate", "resource"); ("lemma", "transfer") ];
            callables = [ M.source_callable resource; M.source_callable transfer ];
          }
      else if List.equal String.equal signature.path [ M.protocol_name ] then
        Some
          {
            signature with
            path = [ protocol_name ];
            parameters = [ { C.name = "R"; interface = [ resource_interface ] } ];
            callables =
              List.map
                [
                  M.association_declaration;
                  M.held_declaration;
                  initialize;
                  M.condition_declaration;
                  M.condition_initialization_declaration;
                ]
                ~f:M.source_callable;
          }
      else None)
