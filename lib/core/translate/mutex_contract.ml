(** Exclusive native mutex initialization and acquisition capabilities. *)

module R = Raven_api

let module_name = "Caravan$Mutex$Raw"
let ident ~loc text = R.Ident.make ~loc text
let local ~loc text = R.Name.make ~loc text
let member ~loc text = R.Name.make ~loc ~path:[ module_name ] text
let variable ~loc text = R.Expr.var ~loc (local ~loc text)

let support ~loc () =
  let library text = R.Name.make ~loc ~path:[ "Library" ] text in
  let named text = R.Type.named ~loc (local ~loc text) [] in
  let reference text = R.Var.make ~loc (ident ~loc text) (R.Type.ref ~loc) in
  let m = variable ~loc "m" in
  let self = variable ~loc "self" in
  let call path text arguments =
    R.Expr.call ~loc (R.Name.make ~loc ~path text) arguments
  in
  let field text = R.Expr.field ~loc m (local ~loc text) in
  let own text value = R.Expr.own ~loc [ field text; value ] in
  let initialization = call [ "Token" ] "excl" [ R.Expr.tuple ~loc [] ] in
  let owner value = call [ "Owner" ] "excl" [ value ] in
  let fresh = R.Expr.call ~loc (local ~loc "fresh") [ m ] in
  let held value = R.Expr.call ~loc (local ~loc "held") [ m; value ] in
  let predicate text formals body =
    R.Member.callable
      (R.Callable.func ~loc ~kind:Pred ~formals (ident ~loc text) (Some body))
  in
  let exclusive text formals resource unfoldings =
    R.Member.callable
      (R.Callable.proc ~loc ~kind:Lemma ~formals
         ~requires:[ R.Spec.make resource ]
         ~ensures:[ R.Spec.make (R.Expr.bool ~loc false) ]
         (ident ~loc text)
         (Some
            (unfoldings @ [ R.Stmt.assert_ ~loc (R.Spec.make (R.Expr.bool ~loc false)) ])))
  in
  [
    R.Member.module_ ~loc (ident ~loc module_name)
      [
        R.Member.instance ~loc
          ~def:(library "Excl", [ R.Type.named ~loc (library "Unit") [] ])
          (ident ~loc "Token") (library "Excl");
        R.Member.instance ~loc
          ~def:(library "Excl", [ R.Type.ref ~loc ])
          (ident ~loc "Owner") (library "Excl");
        R.Member.field ~loc ~ghost:true
          (ident ~loc "initialization_token")
          (named "Token");
        R.Member.field ~loc ~ghost:true (ident ~loc "acquisition_owner") (named "Owner");
        predicate "fresh"
          [ reference "m" ]
          (R.Expr.binary ~loc And
             (own "initialization_token" initialization)
             (own "acquisition_owner" (owner (R.Expr.null ~loc))));
        predicate "held"
          [ reference "m"; reference "self" ]
          (own "acquisition_owner" (owner self));
        R.Member.callable
          (R.Callable.proc ~loc
             ~returns:[ reference "m" ]
             ~ensures:[ R.Spec.make fresh ]
             (ident ~loc "create")
             (Some
                [
                  R.Stmt.assign ~loc [ m ]
                    (R.Stmt.new_rhs
                       [
                         (local ~loc "initialization_token", Some initialization);
                         (local ~loc "acquisition_owner", Some (owner (R.Expr.null ~loc)));
                       ]);
                  R.Stmt.fold ~loc (local ~loc "fresh") [ m ];
                  R.Stmt.return ~loc [ m ];
                ]));
        exclusive "fresh_exclusive"
          [ reference "m" ]
          (R.Expr.binary ~loc And fresh fresh)
          [
            R.Stmt.unfold ~loc (local ~loc "fresh") [ m ];
            R.Stmt.unfold ~loc (local ~loc "fresh") [ m ];
          ];
        exclusive "held_exclusive"
          [ reference "m"; reference "first"; reference "second" ]
          (R.Expr.binary ~loc And
             (held (variable ~loc "first"))
             (held (variable ~loc "second")))
          [
            R.Stmt.unfold ~loc (local ~loc "held") [ m; variable ~loc "first" ];
            R.Stmt.unfold ~loc (local ~loc "held") [ m; variable ~loc "second" ];
          ];
      ];
  ]

let create ~loc = R.Expr.call ~loc (member ~loc "create") []
let fresh ~loc mutex = R.Expr.call ~loc (member ~loc "fresh") [ mutex ]
let held ~loc mutex self = R.Expr.call ~loc (member ~loc "held") [ mutex; self ]
let resource_interface = "Caravan$Mutex$Resource"
let protocol_name = "Caravan$Mutex$Protocol"
let execution_name = "Caravan$Mutex$Execution"
let execution_interface = "Caravan$Mutex$ExecutionSignature"
let native_name = "Caravan$Mutex$Native"
let held_set_type ~loc = R.Type.fin_set ~loc (R.Type.ref ~loc)
let empty_held_set ~loc = R.Expr.annotated (R.Expr.set ~loc []) (held_set_type ~loc)

let acquired_set ~loc held_set mutex =
  R.Expr.binary ~loc Union held_set (R.Expr.set ~loc [ mutex ])

let released_set ~loc held_set mutex =
  R.Expr.binary ~loc Diff held_set (R.Expr.set ~loc [ mutex ])

let execution_call ~loc text arguments =
  R.Expr.call ~loc (R.Name.make ~loc ~path:[ execution_name ] text) arguments

let execution_context ~loc self held_set =
  execution_call ~loc "context" [ self; held_set ]

let execution_finished ~loc self = execution_call ~loc "finished" [ self ]
let start ~loc = execution_call ~loc "start" []
let finish ~loc self = execution_call ~loc "finish" [ self ]
let snapshot ~loc self = execution_call ~loc "snapshot" [ self ]

module C = Checked_signatures

type public_type = Carrier | Native_mutex | Native_condition | Owner | Resource

type public_parameter = {
  parameter_name : string;
  parameter_type : public_type;
  parameter_ghost : bool;
  parameter_implicit : bool;
}

type public_declaration = {
  declaration_name : string;
  declaration_kind : R.Ast.Callable.call_kind;
  declaration_parameters : public_parameter list;
  declaration_results : public_parameter list;
}

let public_parameter ?(ghost = false) ?(implicit = false) parameter_name parameter_type =
  {
    parameter_name;
    parameter_type;
    parameter_ghost = ghost;
    parameter_implicit = implicit;
  }

let resource_declaration =
  {
    declaration_name = "resource";
    declaration_kind = R.Ast.Callable.Pred;
    declaration_parameters = [ public_parameter "r" Carrier ];
    declaration_results = [];
  }

let association_declaration =
  {
    declaration_name = "is_mutex";
    declaration_kind = R.Ast.Callable.Invariant;
    declaration_parameters = [ public_parameter "m" Native_mutex ];
    declaration_results = [ public_parameter ~ghost:true ~implicit:true "r" Resource ];
  }

let held_declaration =
  {
    declaration_name = "held";
    declaration_kind = R.Ast.Callable.Pred;
    declaration_parameters =
      [ public_parameter "m" Native_mutex; public_parameter ~ghost:true "self" Owner ];
    declaration_results = [];
  }

let initialization_declaration =
  {
    declaration_name = "initialize";
    declaration_kind = R.Ast.Callable.Lemma;
    declaration_parameters =
      [ public_parameter "m" Native_mutex; public_parameter ~ghost:true "r" Resource ];
    declaration_results = [];
  }

let condition_declaration =
  {
    declaration_name = "is_condition";
    declaration_kind = R.Ast.Callable.Invariant;
    declaration_parameters = [ public_parameter "c" Native_condition ];
    declaration_results = [ public_parameter ~ghost:true ~implicit:true "m" Native_mutex ];
  }

let condition_initialization_declaration =
  {
    declaration_name = "initialize_condition";
    declaration_kind = R.Ast.Callable.Lemma;
    declaration_parameters =
      [
        public_parameter "c" Native_condition;
        public_parameter ~ghost:true "m" Native_mutex;
      ];
    declaration_results = [];
  }

let public_variables ~loc parameters =
  List.map
    (fun parameter ->
      let typ =
        match parameter.parameter_type with
        | Carrier | Native_mutex -> R.Type.named ~loc (local ~loc "T") []
        | Native_condition -> Condition_contract.typ ~loc
        | Resource -> R.Type.named ~loc (local ~loc "R") []
        | Owner -> R.Type.ref ~loc
      in
      R.Var.make ~loc ~ghost:parameter.parameter_ghost
        ~implicit:parameter.parameter_implicit
        (ident ~loc parameter.parameter_name)
        typ)
    parameters

let public_formals ~loc declaration =
  public_variables ~loc declaration.declaration_parameters

let public_returns ~loc declaration =
  public_variables ~loc declaration.declaration_results

let source_callable declaration : C.callable =
  let typ = function
    | Carrier | Native_mutex -> C.Named ([ "T" ], [])
    | Native_condition -> C.Named ([ Condition_contract.type_name ], [])
    | Resource -> C.Named ([ "R" ], [])
    | Owner -> C.Ref
  in
  let variables parameters =
    List.map
      (fun parameter -> (parameter.parameter_name, typ parameter.parameter_type))
      parameters
  in
  let selected predicate parameters =
    List.filter_map
      (fun parameter ->
        if predicate parameter then Some parameter.parameter_name else None)
      parameters
  in
  {
    operation =
      {
        name = declaration.declaration_name;
        inputs = variables declaration.declaration_parameters;
        outputs = variables declaration.declaration_results;
      };
    kind = declaration.declaration_kind;
    ghost_inputs =
      selected
        (fun parameter -> parameter.parameter_ghost)
        declaration.declaration_parameters;
    implicit_inputs =
      selected
        (fun parameter -> parameter.parameter_implicit)
        declaration.declaration_parameters;
    ghost_outputs =
      selected
        (fun parameter -> parameter.parameter_ghost)
        declaration.declaration_results;
    implicit_outputs =
      selected
        (fun parameter -> parameter.parameter_implicit)
        declaration.declaration_results;
  }

let source_signatures () : C.module_signature list =
  let carrier ~rep definition : C.type_member =
    { name = "T"; rep; definition; constructors = []; destructors = [] }
  in
  [
    {
      path = [ resource_interface ];
      interface = true;
      parameters = [];
      implements = [ [ "Library"; "Type" ] ];
      required_members = [ ("predicate", resource_declaration.declaration_name) ];
      types = [ carrier ~rep:true None ];
      operations = [];
      callables = [ source_callable resource_declaration ];
      constants = [];
    };
    {
      path = [ protocol_name ];
      interface = false;
      parameters = [ { name = "R"; interface = [ resource_interface ] } ];
      implements = [];
      required_members = [];
      types = [ carrier ~rep:false (Some C.Ref) ];
      operations = [];
      callables =
        List.map source_callable
          [
            association_declaration;
            held_declaration;
            initialization_declaration;
            condition_declaration;
            condition_initialization_declaration;
          ];
      constants = [];
    };
  ]

let resource_signature ~loc () =
  R.Member.module_ ~loc ~interface:true
    ~implements:[ (R.Name.make ~loc ~path:[ "Library" ] "Type", []) ]
    (ident ~loc resource_interface)
    [
      R.Member.type_ ~loc ~rep:true (ident ~loc "T") None;
      R.Member.callable
        (R.Callable.func ~loc ~kind:Pred
           ~formals:(public_formals ~loc resource_declaration)
           (ident ~loc resource_declaration.declaration_name)
           None);
    ]

let execution_support ~loc () =
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
  let finished = R.Expr.call ~loc (local ~loc "finished") [ self ] in
  let declaration text formals body =
    R.Member.callable (R.Callable.func ~loc ~kind:Pred ~formals (ident ~loc text) body)
  in
  let context_declaration body =
    R.Member.callable
      (R.Callable.func ~loc ~kind:Pred
         ~formals:[ reference "self" ]
         ~returns:[ held_set_parameter ~implicit:true "held_set" ]
         (ident ~loc "context") body)
  in
  let start body =
    R.Member.callable
      (R.Callable.proc ~loc
         ~returns:[ reference "self" ]
         ~ensures:[ R.Spec.make (context self (empty_held_set ~loc)) ]
         (ident ~loc "start") body)
  in
  let finish body =
    R.Member.callable
      (R.Callable.proc ~loc
         ~formals:[ reference "self" ]
         ~requires:[ R.Spec.make (context self (empty_held_set ~loc)) ]
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
  [
    R.Member.module_ ~loc ~interface:true
      (ident ~loc execution_interface)
      [
        context_declaration None;
        declaration "finished" [ reference "self" ] None;
        start None;
        finish None;
        snapshot None;
        exclusive None;
      ];
    R.Member.module_ ~loc ~sealed:true
      ~implements:[ (local ~loc execution_interface, []) ]
      (ident ~loc execution_name)
      [
        R.Member.instance ~loc
          ~def:(R.Name.make ~loc ~path:[ "Library" ] "Excl", [ held_set_type ~loc ])
          (ident ~loc "Token")
          (R.Name.make ~loc ~path:[ "Library" ] "Excl");
        R.Member.field ~loc ~ghost:true
          (ident ~loc "execution_token")
          (R.Type.named ~loc (local ~loc "Token") []);
        context_declaration (Some (own held_set));
        declaration "finished" [ reference "self" ] (Some (own (empty_held_set ~loc)));
        start
          (Some
             [
               R.Stmt.ghost_block ~loc
                 [
                   R.Stmt.assign ~loc [ self ]
                     (R.Stmt.new_rhs
                        [
                          ( local ~loc "execution_token",
                            Some (capability (empty_held_set ~loc)) );
                        ]);
                 ];
               R.Stmt.fold ~loc (local ~loc "context") [ self; empty_held_set ~loc ];
               R.Stmt.return ~loc [ self ];
             ]);
        finish
          (Some
             [
               R.Stmt.unfold ~loc (local ~loc "context") [ self; empty_held_set ~loc ];
               R.Stmt.fold ~loc (local ~loc "finished") [ self ];
             ]);
        snapshot
          (Some
             [ R.Stmt.assign ~loc [ variable ~loc "current" ] (R.Stmt.expr_rhs held_set) ]);
        exclusive
          (Some
             [
               R.Stmt.unfold ~loc (local ~loc "context") [ self; variable ~loc "first" ];
               R.Stmt.unfold ~loc (local ~loc "context") [ self; variable ~loc "second" ];
               R.Stmt.assert_ ~loc (R.Spec.make (R.Expr.bool ~loc false));
             ]);
      ];
  ]

let protocol ~loc () =
  let reference ?(ghost = true) text =
    let typ = if ghost then R.Type.ref ~loc else R.Type.named ~loc (local ~loc "T") [] in
    R.Var.make ~loc ~ghost (ident ~loc text) typ
  in
  let resource_type = R.Type.named ~loc (local ~loc "R") [] in
  let resource =
    R.Var.make ~loc ~ghost:true ~implicit:true (ident ~loc "r") resource_type
  in
  let held_set =
    R.Var.make ~loc ~ghost:true ~implicit:true (ident ~loc "held_set")
      (held_set_type ~loc)
  in
  let mutex = variable ~loc "m" in
  let self = variable ~loc "self" in
  let r = variable ~loc "r" in
  let held_values = variable ~loc "held_set" in
  let association = R.Expr.call ~loc (local ~loc "is_mutex") [ mutex; r ] in
  let condition = variable ~loc "c" in
  let condition_association =
    R.Expr.call ~loc (local ~loc "is_condition") [ condition; mutex ]
  in
  let protected = R.Expr.call ~loc (R.Name.make ~loc ~path:[ "R" ] "resource") [ r ] in
  let current = execution_context ~loc self held_values in
  let contains = R.Expr.binary ~loc In mutex held_values in
  let not_held = R.Expr.not_ ~loc contains in
  let conjunction expressions =
    List.fold_left (R.Expr.binary ~loc And) (R.Expr.bool ~loc true) expressions
  in
  let kernel ?(kind = R.Callable.Proc) text formals returns requires ensures =
    R.Member.free
      (R.Member.callable
         (R.Callable.proc ~loc ~kind ~formals ~returns
            ~requires:[ R.Spec.make (conjunction requires) ]
            ~ensures:[ R.Spec.make (conjunction ensures) ]
            (ident ~loc text) None))
  in
  let notification text =
    kernel text
      [
        R.Var.make ~loc (ident ~loc "c") (Condition_contract.typ ~loc);
        reference "self";
        R.Var.make ~loc ~ghost:true ~implicit:true (ident ~loc "m") (R.Type.ref ~loc);
        held_set;
      ]
      []
      [ current; condition_association ]
      [ current; condition_association ]
  in
  let acquire =
    conjunction
      [
        not_held;
        execution_context ~loc self (acquired_set ~loc held_values mutex);
        held ~loc mutex self;
        protected;
      ]
  in
  let operation_formals =
    [ reference ~ghost:false "m"; reference "self"; resource; held_set ]
  in
  R.Member.module_ ~loc
    ~params:[ (ident ~loc "R", local ~loc resource_interface) ]
    (ident ~loc protocol_name)
    [
      R.Member.type_ ~loc (ident ~loc "T") (Some (R.Type.ref ~loc));
      R.Member.free
        (R.Member.callable
           (R.Callable.func ~loc ~kind:Inv
              ~formals:(public_formals ~loc association_declaration)
              ~returns:(public_returns ~loc association_declaration)
              (ident ~loc association_declaration.declaration_name)
              None));
      R.Member.free
        (R.Member.callable
           (R.Callable.func ~loc ~kind:Inv
              ~formals:(public_formals ~loc condition_declaration)
              ~returns:(public_returns ~loc condition_declaration)
              (ident ~loc condition_declaration.declaration_name)
              None));
      kernel ~kind:Lemma condition_initialization_declaration.declaration_name
        (public_formals ~loc condition_initialization_declaration)
        []
        [ Condition_contract.fresh ~loc condition ]
        [ condition_association ];
      R.Member.callable
        (R.Callable.func ~loc ~kind:Pred ~inline:true
           ~formals:(public_formals ~loc held_declaration)
           (ident ~loc held_declaration.declaration_name)
           (Some (held ~loc mutex self)));
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:[ reference ~ghost:false "m"; reference "first"; reference "second" ]
           ~requires:
             [
               R.Spec.make
                 (R.Expr.binary ~loc And
                    (held ~loc mutex (variable ~loc "first"))
                    (held ~loc mutex (variable ~loc "second")));
             ]
           ~ensures:[ R.Spec.make (R.Expr.bool ~loc false) ]
           (ident ~loc "held_exclusive")
           (Some
              [
                R.Stmt.call ~loc
                  (R.Expr.call ~loc
                     (member ~loc "held_exclusive")
                     [ mutex; variable ~loc "first"; variable ~loc "second" ]);
              ]));
      kernel ~kind:Lemma initialization_declaration.declaration_name
        (public_formals ~loc initialization_declaration)
        []
        [ fresh ~loc mutex; protected ]
        [ association ];
      kernel "lock" operation_formals []
        [ current; association; not_held ]
        [ association; acquire ];
      kernel "unlock" operation_formals []
        [ current; contains; association; held ~loc mutex self; protected ]
        [ association; execution_context ~loc self (released_set ~loc held_values mutex) ];
      kernel "wait"
        (R.Var.make ~loc (ident ~loc "c") (Condition_contract.typ ~loc)
        :: operation_formals)
        []
        [
          current;
          contains;
          association;
          condition_association;
          held ~loc mutex self;
          protected;
        ]
        [ current; association; condition_association; held ~loc mutex self; protected ];
      notification "signal";
      notification "broadcast";
      kernel "try_lock" operation_formals
        [ R.Var.make ~loc (ident ~loc "success") (R.Type.bool ~loc) ]
        [ current; association ]
        [ association; R.Expr.ite ~loc (variable ~loc "success") acquire current ];
    ]

let native_support ~loc () =
  let self = variable ~loc "self" in
  let held_set = variable ~loc "held_set" in
  let mutex = variable ~loc "m" in
  let current = execution_context ~loc self held_set in
  R.Member.module_ ~loc (ident ~loc native_name)
    [
      R.Member.free
        (R.Member.callable
           (R.Callable.proc ~loc
              ~formals:
                [
                  R.Var.make ~loc ~ghost:true (ident ~loc "self") (R.Type.ref ~loc);
                  R.Var.make ~loc ~ghost:true ~implicit:true (ident ~loc "held_set")
                    (held_set_type ~loc);
                ]
              ~returns:[ R.Var.make ~loc (ident ~loc "m") (R.Type.ref ~loc) ]
              ~requires:[ R.Spec.make current ]
              ~ensures:
                [
                  R.Spec.make current;
                  R.Spec.make (fresh ~loc mutex);
                  R.Spec.make (R.Expr.not_ ~loc (R.Expr.binary ~loc In mutex held_set));
                ]
              (ident ~loc "create") None));
    ]

let create_in_execution ~loc self =
  R.Expr.call ~loc (R.Name.make ~loc ~path:[ native_name ] "create") [ self ]

let protocol_support ~loc () =
  (resource_signature ~loc () :: execution_support ~loc ())
  @ [ native_support ~loc (); protocol ~loc () ]

let complete_support ~loc () =
  support ~loc () @ Condition_contract.support ~loc () @ protocol_support ~loc ()

let instance ~loc ~name ~resource =
  let target = local ~loc protocol_name in
  R.Member.instance ~loc
    ~def:(target, [ R.Type.named ~loc (Qualified_name.raven ~loc resource) [] ])
    (ident ~loc name) target

let protocol_call ~loc ~facade text arguments =
  let target = Qualified_name.{ path = facade.path @ [ facade.name ]; name = text } in
  R.Expr.call ~loc (Qualified_name.raven ~loc target) arguments

let is_mutex ~loc ~facade mutex resource =
  protocol_call ~loc ~facade "is_mutex" [ mutex; resource ]

let initialize ~loc ~facade mutex resource =
  protocol_call ~loc ~facade "initialize" [ mutex; resource ]

let lock ~loc ~facade mutex self = protocol_call ~loc ~facade "lock" [ mutex; self ]
let unlock ~loc ~facade mutex self = protocol_call ~loc ~facade "unlock" [ mutex; self ]

let try_lock ~loc ~facade mutex self =
  protocol_call ~loc ~facade "try_lock" [ mutex; self ]
