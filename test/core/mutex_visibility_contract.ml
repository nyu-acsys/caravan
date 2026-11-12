(** Visibility-aware mutex wrappers use the shared release/acquire envelopes. *)

open Base
module R = Raven_api
module E = Caravan_core.Execution_contract
module M = Caravan_core.Mutex_contract
module V = Caravan_core.Mutex_visibility_contract

let loc = R.Loc.none
let id = R.Ident.make ~loc
let name = R.Name.make ~loc
let var text = R.Expr.var ~loc (name text)
let reference text = R.Var.make ~loc ~ghost:true (id text) (R.Type.ref ~loc)

let resource owner =
  R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Resource" ] "resource") [ owner; var "r" ]

let seen owner cut =
  Caravan_core.Visibility_contract.seen ~loc ~module_name:E.module_name owner
    (R.Expr.set ~loc [ cut ])

let cap = E.visibility_handoff ~loc (var "source") (var "target")

let resource_module =
  R.Member.module_ ~loc
    ~implements:[ (name V.resource_interface, []) ]
    (id "Resource")
    [
      R.Member.type_ ~loc ~rep:true (id "T") (Some (R.Type.ref ~loc));
      R.Member.callable
        (R.Callable.func ~loc ~kind:Pred
           ~formals:
             [
               R.Var.make ~loc (id "self") (R.Type.ref ~loc);
               R.Var.make ~loc (id "r") (R.Type.ref ~loc);
             ]
           (id "resource")
           (Some (seen (var "self") (var "r"))));
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:[ reference "source"; reference "target"; reference "r" ]
           ~requires:
             [ R.Spec.make (R.Expr.binary ~loc And cap (resource (var "source"))) ]
           ~ensures:[ R.Spec.make (R.Expr.binary ~loc And cap (resource (var "target"))) ]
           (id "transfer")
           (Some
              [
                R.Stmt.unfold ~loc
                  (R.Name.make ~loc ~path:[ "Resource" ] "resource")
                  [ var "source"; var "r" ];
                R.Stmt.call ~loc
                  (E.visibility_transfer ~loc (var "source") (var "target")
                     (R.Expr.set ~loc [ var "r" ]));
                R.Stmt.fold ~loc
                  (R.Name.make ~loc ~path:[ "Resource" ] "resource")
                  [ var "target"; var "r" ];
              ]));
    ]

let guard text args = R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Guard" ] text) args
let invoke expression = R.Stmt.call ~loc expression

let local_owner text expression =
  R.Stmt.local ~loc ~ghost:true ~typ:(R.Type.ref ~loc) ~init:(R.Stmt.expr_rhs expression)
    (id text)

let empty = E.empty_held_set ~loc
let source = var "source"
let target = var "target"
let mutex = var "mutex"
let cut = var "r"
let resource_name = R.Name.make ~loc ~path:[ "Resource" ] "resource"

type probe = Acquire | No_acquire | Failed_try | Notify of string

let client probe =
  R.Member.callable
    (R.Callable.proc ~loc
       ~formals:[ reference "source"; reference "r" ]
       ~requires:
         (List.map
            [
              E.context ~loc source empty;
              E.visibility_context ~loc source;
              seen source cut;
            ]
            ~f:R.Spec.make)
       (id "client")
       (Some
          (local_owner "target" (E.start ~loc)
          @ R.Stmt.local ~loc ~typ:(R.Type.ref ~loc)
              ~init:(R.Stmt.expr_rhs (M.create_in_execution ~loc source))
              (id "mutex")
          @ [
              R.Stmt.fold ~loc resource_name [ source; cut ];
              invoke (guard "initialize" [ mutex; source; cut ]);
            ]
          @
          match probe with
          | Acquire ->
              [
                invoke (guard "lock" [ mutex; target; cut; empty ]);
                R.Stmt.unfold ~loc resource_name [ target; cut ];
                R.Stmt.assert_ ~loc (R.Spec.make (seen target cut));
              ]
          | No_acquire -> [ R.Stmt.assert_ ~loc (R.Spec.make (seen target cut)) ]
          | Notify operation ->
              R.Stmt.local ~loc
                ~typ:(Caravan_core.Condition_contract.typ ~loc)
                ~init:(R.Stmt.expr_rhs (Caravan_core.Condition_contract.create ~loc))
                (id "condition")
              @ [
                  invoke (guard "initialize_condition" [ var "condition"; mutex ]);
                  invoke (guard operation [ var "condition"; target; mutex; empty ]);
                  R.Stmt.assert_ ~loc (R.Spec.make (seen target cut));
                ]
          | Failed_try ->
              R.Stmt.local ~loc ~typ:(R.Type.bool ~loc)
                ~init:(R.Stmt.expr_rhs (guard "try_lock" [ mutex; target; cut; empty ]))
                (id "success")
              @ [
                  R.Stmt.if_ ~loc (var "success") []
                    [ R.Stmt.assert_ ~loc (R.Spec.make (seen target cut)) ];
                ])))

let check probe =
  let result =
    R.verify
      (R.Program.make ~loc
         (Caravan_core.Prelude.value_signature
         :: (M.complete_support ~loc ~visibility:true ()
            @ V.support ~loc ()
            @ [
                resource_module;
                R.Member.instance ~loc
                  ~def:(name V.protocol_name, [ R.Type.named ~loc (name "Resource") [] ])
                  (id "Guard") (name V.protocol_name);
                client probe;
              ])))
  in
  if Poly.equal probe Acquire then (
    if not result.verified then
      failwith
        (String.concat ~sep:"\n" (List.map result.diagnostics ~f:R.Diagnostic.to_string)))
  else (
    assert (not result.verified);
    assert (
      List.exists result.diagnostics ~f:(fun diagnostic ->
          Poly.equal diagnostic.R.Diagnostic.code (Some R.Diagnostic.Assertion))))

let () =
  List.iter
    [ Acquire; No_acquire; Failed_try; Notify "signal"; Notify "broadcast" ]
    ~f:check
