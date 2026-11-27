(** Exclusive initialization of native condition-to-mutex associations. *)

module R = Raven_api

let module_name = "Caravan$Condition$Raw"
let type_name = "Caravan$Condition$T"
let typ ~loc = R.Type.named ~loc (R.Name.make ~loc type_name) []
let member ~loc text = R.Name.make ~loc ~path:[ module_name ] text
let create ~loc = R.Expr.call ~loc (member ~loc "create") []
let fresh ~loc condition = R.Expr.call ~loc (member ~loc "fresh") [ condition ]

let support ~loc () =
  let ident text = R.Ident.make ~loc text in
  let local text = R.Name.make ~loc text in
  let condition = R.Expr.var ~loc (local "c") in
  let token =
    R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Token" ] "excl") [ R.Expr.tuple ~loc [] ]
  in
  let fresh = R.Expr.call ~loc (local "fresh") [ condition ] in
  [
    R.Member.type_ ~loc (ident type_name) (Some (R.Type.ref ~loc));
    R.Member.module_ ~loc (ident module_name)
      [
        R.Member.instance ~loc
          ~def:
            ( R.Name.make ~loc ~path:[ "Library" ] "Excl",
              [ R.Type.named ~loc (R.Name.make ~loc ~path:[ "Library" ] "Unit") [] ] )
          (ident "Token")
          (R.Name.make ~loc ~path:[ "Library" ] "Excl");
        R.Member.field ~loc ~ghost:true
          (ident "initialization_token")
          (R.Type.named ~loc (local "Token") []);
        R.Member.callable
          (R.Callable.func ~loc ~kind:Pred
             ~formals:[ R.Var.make ~loc (ident "c") (typ ~loc) ]
             (ident "fresh")
             (Some
                (R.Expr.own ~loc
                   [ R.Expr.field ~loc condition (local "initialization_token"); token ])));
        R.Member.callable
          (R.Callable.proc ~loc
             ~returns:[ R.Var.make ~loc (ident "c") (typ ~loc) ]
             ~ensures:[ R.Spec.make fresh ]
             (ident "create")
             (Some
                [
                  R.Stmt.assign ~loc [ condition ]
                    (R.Stmt.new_rhs [ (local "initialization_token", Some token) ]);
                  R.Stmt.fold ~loc (local "fresh") [ condition ];
                  R.Stmt.return ~loc [ condition ];
                ]));
      ];
  ]
