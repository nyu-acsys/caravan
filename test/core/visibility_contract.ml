(** Visibility authority is exclusive, owner-indexed, and supports monotone growth. *)

open Base
module R = Raven_api
module V = Caravan_core.Visibility_contract

let loc = R.Loc.none
let ident = R.Ident.make ~loc
let name = R.Name.make ~loc
let var text = R.Expr.var ~loc (name text)
let binary = R.Expr.binary ~loc
let reference text = R.Var.make ~loc ~ghost:true (ident text) (R.Type.ref ~loc)
let view_parameter text = R.Var.make ~loc ~ghost:true (ident text) (V.view_type ~loc)
let context owner = R.Expr.call ~loc (name "visibility_context") [ owner ]
let seen owner lower = R.Expr.call ~loc (name "visibility_seen") [ owner; lower ]
let singleton cut = R.Expr.set ~loc [ cut ]
let owner = var "owner"
let cut = var "cut"

let start body =
  R.Member.callable
    (R.Callable.proc ~loc
       ~returns:[ reference "owner" ]
       ~ensures:[ R.Spec.make (context owner) ]
       ~opens:(loc, []) (ident "start") body)

let start_body =
  [
    R.Stmt.ghost_block ~loc
      [ R.Stmt.assign ~loc [ owner ] (R.Stmt.new_rhs [ V.initial_field ~loc () ]) ];
    V.fold_initial ~loc owner;
  ]

(* This transition belongs only to the test implementation, behind its signature. *)
let advance =
  R.Member.callable
    (R.Callable.proc ~loc ~kind:Lemma
       ~formals:[ reference "owner"; reference "cut" ]
       ~requires:[ R.Spec.make (context owner) ]
       ~ensures:[ R.Spec.make (context owner); R.Spec.make (seen owner (singleton cut)) ]
       ~opens:(loc, []) (ident "advance")
       (Some
          (R.Stmt.local ~loc ~ghost:true ~typ:(V.view_type ~loc)
             ~init:(R.Stmt.expr_rhs (V.acquire ~loc owner (singleton cut)))
             (ident "acquired"))))

let exercise body =
  R.Member.callable
    (R.Callable.proc ~loc ~kind:Lemma
       ~formals:[ reference "owner"; reference "cut" ]
       ~requires:[ R.Spec.make (context owner) ]
       ~ensures:[ R.Spec.make (context owner); R.Spec.make (seen owner (singleton cut)) ]
       ~opens:(loc, []) (ident "exercise") body)

let exercise_body =
  let call text arguments = R.Expr.call ~loc (name text) arguments in
  let result text value =
    R.Stmt.local ~loc ~ghost:true ~typ:(V.view_type ~loc) ~init:(R.Stmt.expr_rhs value)
      (ident text)
  in
  result "previous" (call "visibility_snapshot" [ owner ])
  @ [ R.Stmt.call ~loc (call "advance" [ owner; cut ]) ]
  @ result "current" (call "visibility_reconcile" [ owner; var "previous" ])
  @ [
      R.Stmt.assert_ ~loc (R.Spec.make (binary Subseteq (var "previous") (var "current")));
    ]
  @ result "acquired" (call "visibility_reconcile" [ owner; singleton cut ])
  @ [
      R.Stmt.assert_ ~loc (R.Spec.make (binary In cut (var "acquired")));
      R.Stmt.call ~loc (call "visibility_duplicate" [ owner; singleton cut ]);
    ]

let exclusive =
  let view = var "view" in
  R.Member.callable
    (R.Callable.proc ~loc ~kind:Lemma
       ~formals:[ reference "owner" ]
       ~requires:[ R.Spec.make (binary And (context owner) (context owner)) ]
       ~ensures:[ R.Spec.make (R.Expr.bool ~loc false) ]
       ~opens:(loc, []) (ident "exclusive")
       (Some
          (R.Stmt.local ~loc ~ghost:true ~typ:(V.view_type ~loc) (ident "view")
          @ [
              R.Stmt.unfold ~loc
                ~witnesses:[ (ident "view", view) ]
                (name "visibility_context") [ owner ];
              R.Stmt.unfold ~loc
                ~witnesses:[ (ident "view", view) ]
                (name "visibility_context") [ owner ];
              R.Stmt.assert_ ~loc (R.Spec.make (R.Expr.bool ~loc false));
            ])))

let support =
  [
    R.Member.module_ ~loc ~interface:true (ident "VisibilitySignature")
      (V.interface_members ~loc () @ [ start None; exercise None ]);
    R.Member.module_ ~loc ~sealed:true
      ~implements:[ (name "VisibilitySignature", []) ]
      (ident "Execution")
      (V.implementation_members ~loc ()
      @ [ start (Some start_body); advance; exercise (Some exercise_body); exclusive ]);
  ]

let external_context = V.context ~loc ~module_name:"Execution"
let external_seen = V.seen ~loc ~module_name:"Execution"

type probe =
  | Valid
  | Duplicate_context
  | Foreign_context
  | Retarget_seen
  | Private_advance
  | Private_acquire
  | Private_acquire_release

let member = function
  | Valid ->
      R.Member.callable
        (R.Callable.proc ~loc
           ~formals:[ reference "cut" ]
           (ident "client")
           (Some
              (R.Stmt.local ~loc ~ghost:true ~typ:(R.Type.ref ~loc)
                 ~init:
                   (R.Stmt.expr_rhs
                      (R.Expr.call ~loc
                         (R.Name.make ~loc ~path:[ "Execution" ] "start")
                         []))
                 (ident "owner")
              @ [
                  R.Stmt.call ~loc
                    (R.Expr.call ~loc
                       (R.Name.make ~loc ~path:[ "Execution" ] "exercise")
                       [ owner; cut ]);
                  R.Stmt.call ~loc
                    (V.duplicate ~loc ~module_name:"Execution" owner (singleton cut));
                ])))
  | Duplicate_context ->
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:[ reference "owner" ]
           ~requires:[ R.Spec.make (external_context owner) ]
           ~ensures:
             [
               R.Spec.make (binary And (external_context owner) (external_context owner));
             ]
           (ident "duplicate_context") (Some []))
  | Foreign_context ->
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:[ reference "owner"; reference "other" ]
           ~requires:
             [
               R.Spec.make (external_context owner);
               R.Spec.make (binary Neq owner (var "other"));
             ]
           (ident "foreign_context")
           (Some
              (R.Stmt.local ~loc ~ghost:true ~typ:(V.view_type ~loc)
                 ~init:
                   (R.Stmt.expr_rhs
                      (V.snapshot ~loc ~module_name:"Execution" (var "other")))
                 (ident "stolen"))))
  | Retarget_seen ->
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:[ reference "owner"; reference "other"; reference "cut" ]
           ~requires:
             [
               R.Spec.make (external_seen owner (singleton cut));
               R.Spec.make (binary Neq owner (var "other"));
             ]
           ~ensures:[ R.Spec.make (external_seen (var "other") (singleton cut)) ]
           (ident "retarget_seen") (Some []))
  | Private_advance ->
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:[ reference "owner"; reference "cut" ]
           ~requires:[ R.Spec.make (external_context owner) ]
           (ident "private_advance")
           (Some
              [
                R.Stmt.call ~loc
                  (R.Expr.call ~loc
                     (R.Name.make ~loc ~path:[ "Execution" ] "advance")
                     [ owner; cut ]);
              ]))
  | (Private_acquire | Private_acquire_release) as probe ->
      let prior = V.empty_view ~loc in
      let method_, arguments =
        if Poly.equal probe Private_acquire_release then
          ("visibility_acquire_release", [ owner; prior; singleton cut ])
        else ("visibility_acquire", [ owner; singleton cut ])
      in
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:[ reference "owner"; reference "cut" ]
           ~requires:
             [
               R.Spec.make (external_context owner);
               R.Spec.make (external_seen owner prior);
             ]
           (ident "private_acquisition")
           (Some
              (R.Stmt.local ~loc ~ghost:true ~typ:(V.view_type ~loc)
                 ~init:
                   (R.Stmt.expr_rhs
                      (R.Expr.call ~loc
                         (R.Name.make ~loc ~path:[ "Execution" ] method_)
                         arguments))
                 (ident "acquired"))))

let check probe expected =
  let result = R.verify (R.Program.make ~loc (support @ [ member probe ])) in
  match expected with
  | None ->
      if not result.verified then
        failwith
          (String.concat ~sep:"\n"
             (List.map result.diagnostics ~f:R.Diagnostic.to_string))
  | Some (`Code code) ->
      assert (not result.verified);
      assert (
        List.exists result.diagnostics ~f:(fun diagnostic ->
            Poly.equal diagnostic.R.Diagnostic.code (Some code)))
  | Some `Private ->
      assert (not result.verified);
      assert (
        List.exists result.diagnostics ~f:(fun diagnostic ->
            String.is_substring diagnostic.R.Diagnostic.message ~substring:"accessible"))

let check_execution ?(after_finish = false) ~mutex ~visibility () =
  let module E = Caravan_core.Execution_contract in
  let client =
    R.Member.callable
      (R.Callable.proc ~loc (ident "execution_client")
         (Some
            (R.Stmt.local ~loc ~ghost:true ~typ:(R.Type.ref ~loc)
               ~init:(R.Stmt.expr_rhs (E.start ~loc))
               (ident "owner")
            @ (if visibility then
                 R.Stmt.local ~loc ~ghost:true ~typ:(V.view_type ~loc)
                   ~init:
                     (R.Stmt.expr_rhs (V.snapshot ~loc ~module_name:E.module_name owner))
                   (ident "initial_view")
               else [])
            @ [ R.Stmt.call ~loc (E.finish ~loc owner) ]
            @
            if after_finish then
              R.Stmt.local ~loc ~ghost:true ~typ:(V.view_type ~loc)
                ~init:(R.Stmt.expr_rhs (V.snapshot ~loc ~module_name:E.module_name owner))
                (ident "finished_view")
            else [])))
  in
  let result =
    R.verify
      (R.Program.make ~loc
         (Caravan_core.Prelude.value_signature
         :: (E.support ~loc ~mutex ~visibility () @ [ client ])))
  in
  if after_finish then (
    assert (not result.verified);
    assert (
      List.exists result.diagnostics ~f:(fun diagnostic ->
          Poly.equal diagnostic.R.Diagnostic.code (Some R.Diagnostic.Precondition))))
  else if not result.verified then
    failwith
      (String.concat ~sep:"\n" (List.map result.diagnostics ~f:R.Diagnostic.to_string))

let () =
  check_execution ~mutex:true ~visibility:false ();
  check_execution ~mutex:false ~visibility:true ();
  check_execution ~mutex:true ~visibility:true ();
  check_execution ~after_finish:true ~mutex:false ~visibility:true ();
  check Valid None;
  check Duplicate_context (Some (`Code R.Diagnostic.Postcondition));
  check Foreign_context (Some (`Code R.Diagnostic.Precondition));
  check Retarget_seen (Some (`Code R.Diagnostic.Postcondition));
  check Private_advance (Some `Private);
  check Private_acquire (Some `Private);
  check Private_acquire_release (Some `Private)
