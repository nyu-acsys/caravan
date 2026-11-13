(** Runtime contracts transfer ownership and retain task-specific outcomes. *)

module R = Raven_api
module D = Caravan_core.Domain_contract
module Q = Caravan_core.Qualified_name

let loc = R.Loc.none
let ident = R.Ident.make ~loc
let name = R.Name.make ~loc
let var text = R.Expr.var ~loc (name text)
let int = R.Expr.int ~loc
let tuple = R.Expr.tuple ~loc
let binary = R.Expr.binary ~loc
let unit_type = R.Type.tuple ~loc []
let unit_value = tuple []
let model = D.create ~namespace:[ "Checks" ] ~prefix:"Domain" ()
let qualified text = Q.{ path = [ "Checks" ]; name = text }
let runtime = qualified "Runtime"
let captures_type = R.Type.tuple ~loc [ R.Type.ref ~loc; R.Type.int ~loc ]

let outcome_type =
  R.Type.named ~loc (R.Name.make ~loc ~path:[ "Library" ] "Option") [ R.Type.int ~loc ]

let none =
  R.Expr.annotated
    (R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Library"; "Option" ] "none") [])
    outcome_type

let raised =
  R.Expr.annotated
    (R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Library"; "Option" ] "some") [ int 7 ])
    outcome_type

let own capture value = R.Expr.own ~loc [ R.Expr.field ~loc capture (name "cell"); value ]
let captures = var "captures"
let captured_cell = R.Expr.tuple_get ~loc captures 0
let captured_value = R.Expr.tuple_get ~loc captures 1
let requires = own captured_cell captured_value

let task ~unit_result ~throws ~ghost_results =
  let result_type, result_value =
    if unit_result then (unit_type, unit_value)
    else (R.Type.int ~loc, binary Plus captured_value (int 1))
  in
  let ghost_type = if ghost_results then R.Type.int ~loc else unit_type in
  let ghost_value =
    if ghost_results then binary Plus captured_value (int 2) else unit_value
  in
  D.task_instance ~loc ~ghost_results:ghost_type model ~name:"Task"
    ~captures:captures_type ~result:result_type ~outcome:outcome_type ~requires
    ~ensures:
      (binary And
         (own captured_cell (binary Plus captured_value (int 1)))
         (binary And
            (binary Eq (var "result") result_value)
            (binary And
               (binary Eq (var "ghosts") ghost_value)
               (binary Eq (var "outcome") (if throws then raised else none)))))

type probe =
  | Valid
  | Duplicate_join
  | Premature_access
  | Forged_normal
  | Wrong_captures
  | Mutated_ghost

let relay =
  let h = var "h" in
  let captured = var "context" in
  R.Member.callable
    (R.Callable.proc ~loc
       ~formals:
         [
           R.Var.make ~loc (ident "h") (R.Type.ref ~loc);
           R.Var.make ~loc ~ghost:true (ident "context") captures_type;
         ]
       ~returns:[ R.Var.make ~loc (ident "returned") (R.Type.ref ~loc) ]
       ~requires:[ R.Spec.make (D.handle ~loc ~runtime [ h; captured ]) ]
       ~ensures:
         [
           R.Spec.make (D.handle ~loc ~runtime [ var "returned"; captured ]);
           R.Spec.make (binary Eq (var "returned") h);
         ]
       (ident "relay")
       (Some [ R.Stmt.return ~loc [ h ] ]))

let client ~unit_result ~throws ~ghost_results probe =
  let local ?typ text rhs =
    R.Stmt.local ~loc ?typ ~init:(R.Stmt.expr_rhs rhs) (ident text)
  in
  let allocate text value =
    R.Stmt.local ~loc
      ~init:(R.Stmt.new_rhs [ (name "cell", Some (int value)) ])
      (ident text)
  in
  let env text value = tuple [ var text; int value ] in
  let wait variable handle environment =
    R.Stmt.local ~loc
      ~typ:(if unit_result then unit_type else R.Type.int ~loc)
      (ident variable)
    @ R.Stmt.local ~loc ~ghost:true
        ~typ:(if ghost_results then R.Type.int ~loc else unit_type)
        (ident (variable ^ "Ghosts"))
    @ R.Stmt.local ~loc ~typ:outcome_type (ident (variable ^ "Outcome"))
    @ [
        R.Stmt.assign ~loc
          [ var variable; var (variable ^ "Ghosts"); var (variable ^ "Outcome") ]
          (R.Stmt.expr_rhs (D.join ~loc ~runtime (var handle) environment));
      ]
  in
  let result_value = if unit_result then unit_value else int 11 in
  R.Member.callable
    (R.Callable.proc ~loc (ident "client")
       (Some
          (allocate "a" 10 @ allocate "b" 20
          @ [
              R.Stmt.fold ~loc
                (R.Name.make ~loc ~path:[ "Task" ] "precondition")
                [ env "a" 10 ];
            ]
          @ local "first" (D.fork ~loc ~runtime (env "a" 10))
          @ (match probe with
            | Premature_access ->
                local "stolen" (R.Expr.field ~loc (var "a") (name "cell"))
            | Valid | Duplicate_join | Forged_normal | Wrong_captures | Mutated_ghost ->
                [])
          @ [
              R.Stmt.fold ~loc
                (R.Name.make ~loc ~path:[ "Task" ] "precondition")
                [ env "b" 20 ];
            ]
          @ local "second" (D.fork ~loc ~runtime (env "b" 20))
          @ local "alias"
              (R.Expr.call ~loc (name "relay")
                 [ var "first"; D.captures ~loc ~runtime (var "first") ])
          @ [
              R.Stmt.assert_ ~loc
                (R.Spec.make
                   (binary Eq (D.captures ~loc ~runtime (var "alias")) (env "a" 10)));
              R.Stmt.assert_ ~loc
                (R.Spec.make
                   (binary Eq
                      (D.captures ~loc ~runtime (var "second"))
                      (match probe with
                      | Wrong_captures -> env "a" 10
                      | Valid | Duplicate_join | Premature_access | Forged_normal
                      | Mutated_ghost ->
                          env "b" 20)));
            ]
          @ wait "y" "second" (D.captures ~loc ~runtime (var "second"))
          @ wait "x" "alias" (D.captures ~loc ~runtime (var "alias"))
          @ (match probe with
            | Duplicate_join -> wait "duplicate" "first" (env "a" 10)
            | Valid | Premature_access | Forged_normal | Wrong_captures | Mutated_ghost ->
                [])
          @ [
              R.Stmt.unfold ~loc
                (R.Name.make ~loc ~path:[ "Task" ] "postcondition")
                [ env "a" 10; var "x"; var "xGhosts"; var "xOutcome" ];
              R.Stmt.assert_ ~loc (R.Spec.make (binary Eq (var "x") result_value));
              R.Stmt.assert_ ~loc
                (R.Spec.make
                   (binary Eq (var "xOutcome")
                      (match probe with
                      | Forged_normal -> none
                      | Valid | Duplicate_join | Premature_access | Wrong_captures
                      | Mutated_ghost ->
                          if throws then raised else none)));
            ]
          @ (match probe with
            | Mutated_ghost ->
                [
                  R.Stmt.ghost_block ~loc
                    [ R.Stmt.assign ~loc [ var "xGhosts" ] (R.Stmt.expr_rhs (int 13)) ];
                ]
            | Valid | Duplicate_join | Premature_access | Forged_normal | Wrong_captures
              ->
                [])
          @ [
              R.Stmt.assert_ ~loc
                (R.Spec.make
                   (binary Eq (var "xGhosts")
                      (if ghost_results then int 12 else unit_value)));
            ]
          @ local "current" (R.Expr.field ~loc (var "a") (name "cell"))
          @ [ R.Stmt.assert_ ~loc (R.Spec.make (binary Eq (var "current") (int 11))) ])))

let program ~unit_result ~throws ~ghost_results probe =
  R.Program.make ~loc
    [
      R.Member.module_ ~loc (ident "Checks")
        (D.support ~loc model
        @ [
            R.Member.field ~loc (ident "cell") (R.Type.int ~loc);
            task ~unit_result ~throws ~ghost_results;
            D.runtime_instance ~loc model ~name:"Runtime" ~task:(qualified "Task");
            relay;
            client ~unit_result ~throws ~ghost_results probe;
          ]);
    ]

let check ~unit_result ?(throws = false) ?(ghost_results = false) probe expected =
  let select_member =
    match probe with
    | Valid -> None
    | Duplicate_join | Premature_access | Forged_normal | Wrong_captures | Mutated_ghost
      ->
        Some (fun (check : R.Progress.check) -> String.equal check.name "Checks.client")
  in
  let result =
    R.verify ?select_member (program ~unit_result ~throws ~ghost_results probe)
  in
  match expected with
  | None ->
      if not result.verified then
        failwith (String.concat "\n" (List.map R.Diagnostic.to_string result.diagnostics))
  | Some code ->
      assert (not result.verified);
      assert (
        List.exists
          (fun (diagnostic : R.Diagnostic.t) -> diagnostic.code = Some code)
          result.diagnostics)

let () =
  check ~unit_result:false Valid None;
  check ~unit_result:true Valid None;
  check ~unit_result:false ~throws:true Valid None;
  check ~unit_result:false Duplicate_join (Some R.Diagnostic.Precondition);
  check ~unit_result:false Premature_access (Some R.Diagnostic.Permission);
  check ~unit_result:false ~throws:true Forged_normal (Some R.Diagnostic.Assertion);
  check ~unit_result:false Wrong_captures (Some R.Diagnostic.Assertion);
  check ~unit_result:false ~ghost_results:true Valid None;
  check ~unit_result:false ~ghost_results:true Mutated_ghost (Some R.Diagnostic.Assertion)
