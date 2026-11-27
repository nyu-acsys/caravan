(** Check the generated atomic support and fractional ownership at its sealed boundary. *)

open Base
module R = Raven_api
module A = Caravan_core.Atomic_visibility_contract
module V = Caravan_core.Visibility_contract
module P = Caravan_core.Prelude

let loc = R.Loc.none
let ident = R.Ident.make ~loc
let name = R.Name.make ~loc
let var text = R.Expr.var ~loc (name text)
let binary = R.Expr.binary ~loc
let owner = var "owner"
let location = var "location"
let released = var "released"
let value = var "value"
let half = R.Expr.real ~loc 0.5
let view_type = V.view_type ~loc
let context = V.context ~loc ~module_name:"Execution" owner

let ownership fraction =
  R.Expr.call ~loc
    (R.Name.make ~loc ~path:[ "Cell" ] "ownership")
    [ location; value; fraction; released ]

let support =
  [
    P.value_signature;
    P.value_dictionary ~loc ~name:"Value" ~carrier:(R.Type.int ~loc)
      ~unrestricted:(R.Expr.bool ~loc true) ~body:(R.Expr.bool ~loc true);
    R.Member.module_ ~loc ~interface:true (ident "ExecutionSignature")
      (V.interface_members ~loc () @ A.interface_members ~loc ());
    R.Member.module_ ~loc ~sealed:true
      ~implements:[ (name "ExecutionSignature", []) ]
      (ident "Execution")
      (V.implementation_members ~loc () @ A.implementation_members ~loc ());
    R.Member.instance ~loc
      ~def:
        ( R.Name.make ~loc ~path:[ "Execution" ] "Atomic",
          [ R.Type.named ~loc (name "Value") [] ] )
      (ident "Cell")
      (R.Name.make ~loc ~path:[ "Execution" ] "AtomicSignature");
  ]

let fractional_read ~fraction =
  let ghost text typ = R.Var.make ~loc ~ghost:true (ident text) typ in
  R.Member.callable
    (R.Callable.proc ~loc
       ~formals:
         [
           ghost "owner" (R.Type.ref ~loc);
           R.Var.make ~loc (ident "location") (R.Type.ref ~loc);
           ghost "value" (R.Type.int ~loc);
           ghost "released" view_type;
         ]
       ~returns:[ R.Var.make ~loc (ident "result") (R.Type.int ~loc) ]
       ~requires:[ R.Spec.make context; R.Spec.make (ownership fraction) ]
       ~ensures:
         [
           R.Spec.make context;
           R.Spec.make (ownership fraction);
           R.Spec.make (binary Eq (var "result") value);
           R.Spec.make (V.seen ~loc ~module_name:"Execution" owner released);
         ]
       (ident "fractional_read")
       (Some
          [
            R.Stmt.assign ~loc
              [ var "result" ]
              (R.Stmt.expr_rhs
                 (R.Expr.call ~loc
                    (R.Name.make ~loc ~path:[ "Cell" ] "get")
                    [ owner; location ]));
          ]))

let ghost text typ = R.Var.make ~loc ~ghost:true (ident text) typ
let ref_parameter text = ghost text (R.Type.ref ~loc)
let context_of owner = V.context ~loc ~module_name:"Execution" owner
let seen owner lower = V.seen ~loc ~module_name:"Execution" owner lower

let cell_call operation arguments =
  R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Cell" ] operation) arguments

let assign targets expression =
  R.Stmt.assign ~loc (List.map targets ~f:var) (R.Stmt.expr_rhs expression)

let assert_ condition = R.Stmt.assert_ ~loc (R.Spec.make condition)
let local ?(ghost = false) text typ = R.Stmt.local ~loc ~ghost ~typ (ident text)

let publication_chain ~wrong_owner =
  let writer = var "writer" and overwriter = var "overwriter" in
  let reader = var "reader" and bystander = var "bystander" in
  let singleton = R.Expr.set ~loc [ var "cut" ] in
  let result_seen = seen (if wrong_owner then bystander else reader) singleton in
  let contexts = List.map [ writer; overwriter; reader; bystander ] ~f:context_of in
  let published = var "published" and overwritten = var "overwritten" in
  R.Member.callable
    (R.Callable.proc ~loc
       ~formals:
         (List.map
            [ "writer"; "overwriter"; "reader"; "bystander"; "cut" ]
            ~f:ref_parameter)
       ~requires:(List.map (seen writer singleton :: contexts) ~f:R.Spec.make)
       ~ensures:[ R.Spec.make result_seen ]
       (ident "publication_chain")
       (Some
          (local "location" (R.Type.ref ~loc)
          @ local ~ghost:true "published" view_type
          @ local ~ghost:true "prior" view_type
          @ local ~ghost:true "overwritten" view_type
          @ local ~ghost:true "current" view_type
          @ local "result" (R.Type.int ~loc)
          @ [
              assign [ "location"; "published" ]
                (cell_call "make" [ writer; singleton; R.Expr.int ~loc 1 ]);
              assert_ (binary Subseteq singleton published);
              assign [ "prior" ] (V.snapshot ~loc ~module_name:"Execution" overwriter);
              assign [ "overwritten" ]
                (cell_call "set" [ overwriter; var "prior"; location; R.Expr.int ~loc 2 ]);
              assert_ (binary Subseteq published overwritten);
              assign [ "result" ] (cell_call "get" [ reader; location ]);
              assert_ (binary Eq (var "result") (R.Expr.int ~loc 2));
              assign [ "current" ]
                (V.reconcile ~loc ~module_name:"Execution" reader overwritten);
              assert_ (binary In (var "cut") (var "current"));
              R.Stmt.call ~loc
                (V.weaken ~loc ~module_name:"Execution" reader overwritten singleton);
            ])))

let failing_cas =
  let prior = var "prior" and published = var "published" in
  R.Member.callable
    (R.Callable.proc ~loc
       ~formals:
         [
           ref_parameter "owner";
           R.Var.make ~loc (ident "location") (R.Type.ref ~loc);
           R.Var.make ~loc (ident "value") (R.Type.int ~loc);
           ghost "released" view_type;
           ghost "prior" view_type;
         ]
       ~requires:(List.map [ context; seen owner prior; ownership half ] ~f:R.Spec.make)
       ~ensures:(List.map [ context; ownership half; seen owner released ] ~f:R.Spec.make)
       (ident "fractional_failed_cas")
       (Some
          (local "result" (R.Type.bool ~loc)
          @ local ~ghost:true "published" view_type
          @ [
              assign [ "result"; "published" ]
                (cell_call "compare_and_set"
                   [
                     owner;
                     prior;
                     location;
                     R.Expr.bool ~loc true;
                     binary Plus value (R.Expr.int ~loc 1);
                     R.Expr.int ~loc 0;
                   ]);
              assert_ (R.Expr.not_ ~loc (var "result"));
              assert_ (binary Eq published released);
            ])))

let split_ownership =
  R.Member.callable
    (R.Callable.proc ~loc ~kind:Lemma
       ~formals:
         [
           ref_parameter "location";
           ghost "value" (R.Type.int ~loc);
           ghost "released" view_type;
         ]
       ~requires:[ R.Spec.make (ownership (R.Expr.real ~loc 1.0)) ]
       ~ensures:[ R.Spec.make (binary And (ownership half) (ownership half)) ]
       (ident "split_ownership") (Some []))

let free_acquire =
  R.Member.callable
    (R.Callable.proc ~loc
       ~formals:
         [
           ref_parameter "owner";
           R.Var.make ~loc (ident "location") (R.Type.ref ~loc);
           ghost "value" (R.Type.int ~loc);
           ghost "released" view_type;
         ]
       ~requires:[ R.Spec.make context ]
       (ident "free_acquire")
       (Some
          (local "result" (R.Type.int ~loc)
          @ [
              assign [ "result" ]
                (cell_call "get" [ owner; location; value; released; half ]);
            ])))

let verify ?select_member members =
  R.verify ?select_member (R.Program.make ~loc (support @ members))

let expect_failure (text, member) code =
  let result =
    verify
      ~select_member:(fun (check : R.Progress.check) -> String.equal check.name text)
      [ member ]
  in
  assert (not result.verified);
  assert (
    List.exists result.diagnostics ~f:(fun diagnostic ->
        Poly.equal diagnostic.R.Diagnostic.code (Some code)))

let () =
  let valid =
    verify
      [
        fractional_read ~fraction:half;
        publication_chain ~wrong_owner:false;
        failing_cas;
        split_ownership;
      ]
  in
  if not valid.verified then
    failwith
      (String.concat ~sep:"\n" (List.map valid.diagnostics ~f:R.Diagnostic.to_string));
  expect_failure
    ("publication_chain", publication_chain ~wrong_owner:true)
    R.Diagnostic.Postcondition;
  expect_failure ("free_acquire", free_acquire) R.Diagnostic.Precondition
