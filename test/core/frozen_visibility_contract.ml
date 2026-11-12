(** Frozen ownership retains the last writer and requires actual acquired visibility. *)

open Base
module R = Raven_api
module F = Caravan_core.Frozen_visibility_contract
module A = Caravan_core.Atomic_visibility_contract
module V = Caravan_core.Visibility_contract
module P = Caravan_core.Prelude

let loc = R.Loc.none
let ident = R.Ident.make ~loc
let name = R.Name.make ~loc
let var text = R.Expr.var ~loc (name text)
let binary = R.Expr.binary ~loc
let reference = R.Type.ref ~loc
let integer = R.Type.int ~loc
let one = R.Expr.real ~loc 1.0
let half = R.Expr.real ~loc 0.5
let value = var "value"
let owner = var "owner"
let other = var "other"
let location = var "location"
let cut = var "cut"
let singleton cut = R.Expr.set ~loc [ cut ]
let context owner = V.context ~loc ~module_name:"Execution" owner
let seen owner cut = V.seen ~loc ~module_name:"Execution" owner (singleton cut)

let cell_call ?(cell = "Cell") operation arguments =
  R.Expr.call ~loc (R.Name.make ~loc ~path:[ cell ] operation) arguments

let ownership ?cell fraction writer =
  cell_call ?cell "ownership" [ location; value; fraction; writer ]

let frozen = cell_call "frozen" [ location; value; cut ]
let ghost text typ = R.Var.make ~loc ~ghost:true (ident text) typ
let ref_parameter ?(ghost = true) text = R.Var.make ~loc ~ghost (ident text) reference
let local ?(ghost = false) text typ = R.Stmt.local ~loc ~ghost ~typ (ident text)

let assign targets expression =
  R.Stmt.assign ~loc (List.map targets ~f:var) (R.Stmt.expr_rhs expression)

let call operation arguments = R.Stmt.call ~loc (cell_call operation arguments)
let assert_ condition = R.Stmt.assert_ ~loc (R.Spec.make condition)

let tag text typ =
  R.Member.module_ ~loc
    ~implements:[ (R.Name.make ~loc ~path:[ "Library" ] "Type", []) ]
    (ident text)
    [ R.Member.type_ ~loc ~rep:true (ident "T") (Some typ) ]

let instance text tag =
  R.Member.instance ~loc
    ~def:
      ( R.Name.make ~loc ~path:[ "Execution" ] "Frozen",
        [ R.Type.named ~loc (name tag) []; R.Type.named ~loc (name "Value") [] ] )
    (ident text)
    (R.Name.make ~loc ~path:[ "Execution" ] "FrozenSignature")

let support =
  [
    P.value_signature;
    P.value_dictionary ~loc ~name:"Value" ~carrier:integer
      ~unrestricted:(R.Expr.bool ~loc true) ~body:(R.Expr.bool ~loc true);
    tag "FirstTag" integer;
    tag "SecondTag" (R.Type.bool ~loc);
    R.Member.module_ ~loc ~interface:true (ident "ExecutionSignature")
      (V.interface_members ~loc () @ A.interface_members ~loc ()
     @ F.interface_members ~loc ());
    R.Member.module_ ~loc ~sealed:true
      ~implements:[ (name "ExecutionSignature", []) ]
      (ident "Execution")
      (V.implementation_members ~loc ()
      @ A.implementation_members ~loc ()
      @ F.implementation_members ~loc ());
    instance "Cell" "FirstTag";
    instance "OtherCell" "SecondTag";
    R.Member.instance ~loc
      ~def:
        ( R.Name.make ~loc ~path:[ "Execution" ] "Atomic",
          [ R.Type.named ~loc (name "Value") [] ] )
      (ident "Channel")
      (R.Name.make ~loc ~path:[ "Execution" ] "AtomicSignature");
  ]

let procedure ?(lemma = false) text formals requires ensures body =
  R.Member.callable
    (R.Callable.proc ~loc
       ~kind:(if lemma then Lemma else Proc)
       ~formals
       ~requires:(List.map requires ~f:R.Spec.make)
       ~ensures:(List.map ensures ~f:R.Spec.make)
       ~opens:(loc, [ (R.Name.make ~loc ~path:[ "Cell" ] "frozen", []) ])
       (ident text) (Some body))

let allocate =
  local "location" reference
  @ [ assign [ "location" ] (cell_call "make" [ owner; value ]) ]

let freeze executing =
  local ~ghost:true "cut" reference
  @ [ assign [ "cut" ] (cell_call "freeze" [ executing; location ]) ]

let read_frozen executing =
  local "result" integer
  @ [
      assign [ "result" ] (cell_call "read_frozen" [ executing; location ]);
      assert_ (binary Eq (var "result") value);
    ]

let same_owner =
  procedure "same_owner"
    [ ref_parameter "owner"; R.Var.make ~loc (ident "value") integer ]
    [ context owner ]
    [ context owner ]
    (allocate
    @ [ call "write" [ owner; location; value ] ]
    @ freeze owner @ read_frozen owner
    @ [
        R.Stmt.call ~loc (V.duplicate ~loc ~module_name:"Execution" owner (singleton cut));
        assert_ (binary And frozen frozen);
      ])

let recipient_writes =
  procedure "recipient_writes"
    [
      ref_parameter "owner";
      ref_parameter "other";
      R.Var.make ~loc (ident "value") integer;
    ]
    [ context owner; context other; binary Neq owner other ]
    [ context owner; context other ]
    (allocate
    @ [ call "write" [ other; location; value ] ]
    @ freeze other @ read_frozen other)

let acquired_recipient_writes =
  let view_type = V.view_type ~loc in
  let channel_call operation arguments =
    R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Channel" ] operation) arguments
  in
  procedure "acquired_recipient_writes"
    [
      ref_parameter "owner";
      ref_parameter "other";
      R.Var.make ~loc (ident "value") integer;
    ]
    [ context owner; context other; binary Neq owner other ]
    [ context owner; context other ]
    (allocate
    @ local ~ghost:true "prior" view_type
    @ local ~ghost:true "published" view_type
    @ local "channel" reference @ local "observed" integer
    @ [
        assign [ "prior" ]
          (cell_call "release_private" [ owner; location; R.Expr.bool ~loc true ]);
        assign [ "channel"; "published" ]
          (channel_call "make" [ owner; var "prior"; R.Expr.int ~loc 1 ]);
        assign [ "observed" ] (channel_call "get" [ other; var "channel" ]);
        call "adopt" [ other; location; R.Expr.bool ~loc true; var "published" ];
        call "write" [ other; location; value ];
      ]
    @ freeze other @ read_frozen other)

let split_ownership =
  procedure ~lemma:true "split_ownership"
    [
      ref_parameter "owner";
      ref_parameter ~ghost:false "location";
      R.Var.make ~loc (ident "value") integer;
    ]
    [ ownership one owner ]
    [ ownership half owner; ownership half owner ]
    [ call "split" [ location; R.Expr.bool ~loc true ] ]

let fractional_read =
  procedure "fractional_read"
    [
      ref_parameter "owner";
      ref_parameter ~ghost:false "location";
      R.Var.make ~loc (ident "value") integer;
    ]
    [ context owner; ownership half owner ]
    [ context owner; ownership half owner ]
    (local "result" integer
    @ [
        assign [ "result" ] (cell_call "read_private" [ owner; location ]);
        assert_ (binary Eq (var "result") value);
      ])

let synchronized_read ~wrong_channel =
  let view_type = V.view_type ~loc in
  let channel_call operation arguments =
    R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Channel" ] operation) arguments
  in
  let snapshot =
    [
      assign [ "prior" ]
        (if wrong_channel then V.snapshot ~loc ~module_name:"Execution" owner
         else V.reconcile ~loc ~module_name:"Execution" owner (singleton cut));
    ]
  in
  let make_channel =
    [
      assign [ "channel"; "published" ]
        (channel_call "make" [ owner; var "prior"; R.Expr.int ~loc 1 ]);
    ]
  in
  procedure
    (if wrong_channel then "wrong_channel" else "synchronized_read")
    [
      ref_parameter "owner";
      ref_parameter "other";
      R.Var.make ~loc (ident "value") integer;
    ]
    [ context owner; context other; binary Neq owner other ]
    [ context owner; context other ]
    (local ~ghost:true "prior" view_type
    @ local ~ghost:true "published" view_type
    @ local "channel" reference @ local "observed" integer
    @ (if wrong_channel then snapshot @ make_channel else [])
    @ allocate
    @ [ call "write" [ owner; location; value ] ]
    @ freeze owner
    @ (if wrong_channel then [] else snapshot @ make_channel)
    @ [ assign [ "observed" ] (channel_call "get" [ other; var "channel" ]) ]
    @ (if wrong_channel then []
       else
         [
           R.Stmt.call ~loc
             (V.weaken ~loc ~module_name:"Execution" other (var "published")
                (singleton cut));
         ])
    @ read_frozen other)

let foreign_freeze =
  procedure "foreign_freeze"
    [
      ref_parameter "owner";
      ref_parameter "other";
      ref_parameter ~ghost:false "location";
      R.Var.make ~loc (ident "value") integer;
    ]
    [ context other; ownership one owner; binary Neq owner other ]
    [] (freeze other)

let transferred_private_read =
  procedure "transferred_private_read"
    [
      ref_parameter "owner";
      ref_parameter "other";
      ref_parameter ~ghost:false "location";
      R.Var.make ~loc (ident "value") integer;
    ]
    [ context other; ownership half owner; binary Neq owner other ]
    []
    (local "result" integer
    @ [ assign [ "result" ] (cell_call "read_private" [ other; location ]) ])

let foreign_read =
  procedure "foreign_read"
    [
      ref_parameter "owner";
      ref_parameter "other";
      ref_parameter ~ghost:false "location";
      ref_parameter "cut";
      R.Var.make ~loc (ident "value") integer;
    ]
    [ context other; frozen; seen owner cut; binary Neq owner other ]
    [] (read_frozen other)

let write_after_freeze =
  procedure "write_after_freeze"
    [ ref_parameter "owner"; R.Var.make ~loc (ident "value") integer ]
    [ context owner ]
    []
    (allocate @ freeze owner @ [ call "write" [ owner; location; value ] ])

let refreeze =
  procedure "refreeze"
    [ ref_parameter "owner"; R.Var.make ~loc (ident "value") integer ]
    [ context owner ]
    []
    (allocate @ freeze owner
    @ local ~ghost:true "second_cut" reference
    @ [ assign [ "second_cut" ] (cell_call "freeze" [ owner; location ]) ])

let partial_freeze =
  procedure "partial_freeze"
    [
      ref_parameter "owner";
      ref_parameter ~ghost:false "location";
      R.Var.make ~loc (ident "value") integer;
    ]
    [ context owner; ownership half owner ]
    [] (freeze owner)

let other_field =
  procedure "other_field"
    [
      ref_parameter "owner";
      ref_parameter ~ghost:false "location";
      R.Var.make ~loc (ident "value") integer;
    ]
    [ context owner; ownership one owner ]
    []
    (local "result" integer
    @ [
        assign [ "result" ]
          (cell_call ~cell:"OtherCell" "read_private" [ owner; location ]);
      ])

let duplicate_private =
  procedure ~lemma:true "duplicate_private"
    [
      ref_parameter "owner";
      ref_parameter ~ghost:false "location";
      R.Var.make ~loc (ident "value") integer;
    ]
    [ ownership one owner ]
    [ binary And (ownership one owner) (ownership one owner) ]
    []

let verify members = R.verify (R.Program.make ~loc (support @ members))

let expect_failure member code =
  let result = verify [ member ] in
  if result.verified then failwith "Accepted an invalid frozen-field operation";
  if
    List.exists result.diagnostics ~f:(fun diagnostic ->
        let message = String.lowercase (R.Diagnostic.to_string diagnostic) in
        String.is_substring message ~substring:"timed out"
        || String.is_substring message ~substring:"timeout")
  then failwith "Frozen-field negative regression timed out";
  if
    not
      (List.exists result.diagnostics ~f:(fun diagnostic ->
           Poly.equal diagnostic.R.Diagnostic.code (Some code)))
  then
    failwith
      (String.concat ~sep:"\n" (List.map result.diagnostics ~f:R.Diagnostic.to_string))

let () =
  let valid_members =
    [
      same_owner;
      acquired_recipient_writes;
      split_ownership;
      fractional_read;
      synchronized_read ~wrong_channel:false;
    ]
  in
  let valid = verify valid_members in
  if not valid.verified then
    failwith
      (String.concat ~sep:"\n" (List.map valid.diagnostics ~f:R.Diagnostic.to_string));
  List.iter
    [
      recipient_writes;
      foreign_freeze;
      transferred_private_read;
      foreign_read;
      write_after_freeze;
      refreeze;
      partial_freeze;
      other_field;
      synchronized_read ~wrong_channel:true;
    ]
    ~f:(fun member -> expect_failure member R.Diagnostic.Precondition);
  expect_failure duplicate_private R.Diagnostic.Postcondition
