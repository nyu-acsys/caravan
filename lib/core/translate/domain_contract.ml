(** Trusted fork/join ownership transfer, parameterized by a task's contract. *)

open Base
module R = Raven_api

type t = { signature_name : Qualified_name.t; runtime_name : Qualified_name.t }

let create ~namespace ~prefix () =
  {
    signature_name = Qualified_name.{ path = namespace; name = prefix ^ "$Task" };
    runtime_name = Qualified_name.{ path = namespace; name = prefix ^ "$Runtime" };
  }

let member_name owner member =
  Qualified_name.{ path = owner.path @ [ owner.name ]; name = member }

let reference ~loc qualified = Qualified_name.raven ~loc qualified
let ident ~loc text = R.Ident.make ~loc text
let name ~loc text = R.Name.make ~loc text
let variable ~loc text = R.Expr.var ~loc (name ~loc text)

let parameter ~loc ?(ghost = false) text typ =
  R.Var.make ~loc ~ghost (ident ~loc text) typ

let resource_signature ~loc model =
  let captures = R.Type.named ~loc (name ~loc "Captures") [] in
  let result = R.Type.named ~loc (name ~loc "Result") [] in
  let ghost_results = R.Type.named ~loc (name ~loc "GhostResults") [] in
  let outcome = R.Type.named ~loc (name ~loc "Outcome") [] in
  let predicate text parameters =
    R.Member.callable
      (R.Callable.func ~loc ~kind:Pred ~formals:parameters (ident ~loc text) None)
  in
  R.Member.module_ ~loc ~interface:true
    (ident ~loc model.signature_name.name)
    [
      R.Member.type_ ~loc (ident ~loc "Captures") None;
      R.Member.type_ ~loc (ident ~loc "Result") None;
      R.Member.type_ ~loc (ident ~loc "GhostResults") None;
      R.Member.type_ ~loc (ident ~loc "Outcome") None;
      predicate "precondition" [ parameter ~loc ~ghost:true "captures" captures ];
      predicate "postcondition"
        [
          parameter ~loc ~ghost:true "captures" captures;
          parameter ~loc "result" result;
          parameter ~loc ~ghost:true "ghosts" ghost_results;
          parameter ~loc "outcome" outcome;
        ];
    ]

let runtime_support ~loc model =
  let task_type text = R.Type.named ~loc (R.Name.make ~loc ~path:[ "Task" ] text) [] in
  let captures = parameter ~loc ~ghost:true "captures" (task_type "Captures") in
  let handle = parameter ~loc "h" (R.Type.ref ~loc) in
  let result = parameter ~loc "result" (task_type "Result") in
  let ghosts = parameter ~loc ~ghost:true "ghosts" (task_type "GhostResults") in
  let outcome = parameter ~loc "outcome" (task_type "Outcome") in
  let context = variable ~loc "captures" in
  let ownership = R.Expr.call ~loc (name ~loc "handle") [ variable ~loc "h"; context ] in
  let task_resource text args =
    R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Task" ] text) args
  in
  let procedure text formals returns requires ensures =
    R.Member.callable
      (R.Callable.proc ~loc ~formals ~returns
         ~requires:[ R.Spec.make requires ]
         ~ensures:[ R.Spec.make ensures ]
         ~opens:(loc, []) (ident ~loc text) None)
  in
  R.Member.free
    (R.Member.module_ ~loc
       ~params:[ (ident ~loc "Task", reference ~loc model.signature_name) ]
       (ident ~loc model.runtime_name.name)
       [
         R.Member.field ~loc ~ghost:true (ident ~loc "join_token") (R.Type.ref ~loc);
         R.Member.callable
           (R.Callable.func ~loc ~formals:[ handle ] ~returns:[ captures ]
              (ident ~loc "captures_of") None);
         R.Member.callable
           (R.Callable.func ~loc ~kind:Pred ~formals:[ handle ] (ident ~loc "claim")
              (Some
                 (R.Expr.own ~loc
                    [
                      R.Expr.field ~loc (variable ~loc "h") (name ~loc "join_token");
                      variable ~loc "h";
                    ])));
         R.Member.callable
           (R.Callable.func ~loc ~kind:Pred ~inline:true ~formals:[ handle; captures ]
              (ident ~loc "handle")
              (Some
                 (R.Expr.binary ~loc And
                    (R.Expr.call ~loc (name ~loc "claim") [ variable ~loc "h" ])
                    (R.Expr.binary ~loc Eq
                       (R.Expr.call ~loc (name ~loc "captures_of") [ variable ~loc "h" ])
                       context))));
         procedure "fork" [ captures ] [ handle ]
           (task_resource "precondition" [ context ])
           ownership;
         procedure "join" [ handle; captures ] [ result; ghosts; outcome ] ownership
           (task_resource "postcondition"
              [
                context;
                variable ~loc "result";
                variable ~loc "ghosts";
                variable ~loc "outcome";
              ]);
       ])

let support ~loc model = [ resource_signature ~loc model; runtime_support ~loc model ]

(** Predicate bodies bind [captures], [result], [ghosts], and [outcome]. Unit results use
    the explicit scalar [()] carrier; exceptional outcomes can use [exn option]. *)
let task_instance ~loc ?ghost_results model ~name:instance ~captures ~result ~outcome
    ~requires ~ensures =
  let ghost_results = Option.value ghost_results ~default:(R.Type.tuple ~loc []) in
  let predicate text formals body =
    R.Member.callable
      (R.Callable.func ~loc ~kind:Pred ~formals (ident ~loc text) (Some body))
  in
  R.Member.module_ ~loc
    ~implements:[ (reference ~loc model.signature_name, []) ]
    (ident ~loc instance)
    [
      R.Member.type_ ~loc (ident ~loc "Captures") (Some captures);
      R.Member.type_ ~loc (ident ~loc "Result") (Some result);
      R.Member.type_ ~loc (ident ~loc "GhostResults") (Some ghost_results);
      R.Member.type_ ~loc (ident ~loc "Outcome") (Some outcome);
      predicate "precondition" [ parameter ~loc ~ghost:true "captures" captures ] requires;
      predicate "postcondition"
        [
          parameter ~loc ~ghost:true "captures" captures;
          parameter ~loc "result" result;
          parameter ~loc ~ghost:true "ghosts" ghost_results;
          parameter ~loc "outcome" outcome;
        ]
        ensures;
    ]

let runtime_instance ~loc model ~name:instance ~task =
  let runtime = reference ~loc model.runtime_name in
  R.Member.instance ~loc
    ~def:(runtime, [ R.Type.named ~loc (reference ~loc task) [] ])
    (ident ~loc instance) runtime

let handle ~loc ~runtime args =
  R.Expr.call ~loc (reference ~loc (member_name runtime "handle")) args

let fork ~loc ~runtime captures =
  R.Expr.call ~loc (reference ~loc (member_name runtime "fork")) [ captures ]

let join ~loc ~runtime handle captures =
  R.Expr.call ~loc (reference ~loc (member_name runtime "join")) [ handle; captures ]

let captures ~loc ~runtime handle =
  R.Expr.call ~loc (reference ~loc (member_name runtime "captures_of")) [ handle ]
