(** Atomic cells carry cumulative release views for their executing owner. *)

open Base
module R = Raven_api

let members ~loc ~implementation =
  let ident text = R.Ident.make ~loc text in
  let name text = R.Name.make ~loc text in
  let variable text = R.Expr.var ~loc (name text) in
  let call text arguments = R.Expr.call ~loc (name text) arguments in
  let binary = R.Expr.binary ~loc in
  let value_name text = R.Name.make ~loc ~path:[ "V" ] text in
  let value_type = R.Type.named ~loc (value_name "Carrier") [] in
  let view_type = Visibility_contract.view_type ~loc in
  let reference = R.Type.ref ~loc in
  let real = R.Type.real ~loc in
  let boolean = R.Type.bool ~loc in
  let formal text typ = R.Var.make ~loc (ident text) typ in
  let ghost ?(implicit = false) text typ =
    R.Var.make ~loc ~ghost:true ~implicit (ident text) typ
  in
  let owner = variable "owner" in
  let prior = variable "prior" in
  let location = variable "location" in
  let value = variable "value" in
  let fraction = variable "q" in
  let release = variable "released" in
  let published = variable "published" in
  let view = variable "view" in
  let acquired = variable "acquired" in
  let one = R.Expr.real ~loc 1.0 in
  let positive = binary Gt fraction (R.Expr.real ~loc 0.0) in
  let context = call "visibility_context" [ owner ] in
  let seen lower = call "visibility_seen" [ owner; lower ] in
  let contents = R.Expr.field ~loc location (name "contents") in
  let metadata = R.Expr.field ~loc location (name "release") in
  let raw_ownership value fraction release =
    binary And
      (R.Expr.own ~loc [ contents; value; fraction ])
      (R.Expr.own ~loc [ metadata; release; fraction ])
  in
  let ownership value fraction release =
    call "ownership" [ location; value; fraction; release ]
  in
  let holds value = R.Expr.call ~loc (value_name "holds") [ value ] in
  let body statements = if implementation then Some statements else None in
  let assign target expression =
    R.Stmt.assign ~loc [ target ] (R.Stmt.expr_rhs expression)
  in
  let procedure text arguments returns requires ensures statements =
    R.Member.callable
      (R.Callable.proc ~loc ~atomic:true ~formals:arguments ~returns
         ~requires:(List.map requires ~f:R.Spec.make)
         ~ensures:(List.map ensures ~f:R.Spec.make)
         ~opens:(loc, []) (ident text) (body statements))
  in
  let executing = ghost "owner" reference in
  let previous = ghost "prior" view_type in
  let lower_bound = ghost "lower" view_type in
  let address = formal "location" reference in
  let implicit_state =
    [ ghost ~implicit:true "value" value_type; ghost ~implicit:true "released" view_type ]
  in
  let release_output = ghost ~implicit:true "published" view_type in
  let acquire_from ?prior () =
    R.Stmt.local ~loc ~ghost:true ~typ:view_type
      ~init:(R.Stmt.expr_rhs (Visibility_contract.acquire ~loc ?prior owner release))
      (ident "acquired")
  in
  let acquire = acquire_from () in
  let acquire_prior = acquire_from ~prior () in
  let common_pre fraction = [ context; ownership value fraction release ] in
  let write_post new_value =
    [
      context;
      ownership new_value one published;
      seen published;
      seen prior;
      binary Subseteq prior published;
      seen release;
      binary Subseteq release published;
    ]
  in
  let write_body new_value =
    acquire_prior
    @ [ assign contents new_value; assign metadata acquired; assign published acquired ]
  in
  let new_value = variable "new_value" in
  let old_value = variable "old_value" in
  let result = variable "result" in
  let same = binary Eq value old_value in
  let exact = variable "exact" in
  let changed_value = R.Expr.ite ~loc result new_value value in
  (if implementation then []
   else
     [
       R.Member.field ~loc ~where:(value_name "holds") (ident "contents") value_type;
       R.Member.field ~loc ~ghost:true (ident "release") view_type;
       R.Member.callable
         (R.Callable.func ~loc ~kind:Pred ~inline:true
            ~formals:
              [
                address;
                ghost "value" value_type;
                ghost "q" real;
                ghost "released" view_type;
              ]
            (ident "ownership")
            (Some (raw_ownership value fraction release)));
     ])
  @ [
      procedure "make"
        [ executing; previous; formal "new_value" value_type ]
        [ address; release_output ]
        [ context; seen prior; holds new_value ]
        [
          context;
          ownership new_value one published;
          seen published;
          seen prior;
          binary Subseteq prior published;
        ]
        (R.Stmt.local ~loc ~ghost:true ~typ:view_type
           ~init:(R.Stmt.expr_rhs (Visibility_contract.publish ~loc owner prior))
           (ident "view")
        @ [
            R.Stmt.assign ~loc [ location ]
              (R.Stmt.new_rhs
                 [ (name "contents", Some new_value); (name "release", Some view) ]);
            assign published view;
          ]);
      procedure "get"
        ([ executing; address ] @ implicit_state @ [ ghost ~implicit:true "q" real ])
        [ formal "result" value_type ]
        (common_pre fraction @ [ positive ])
        [
          context; ownership value fraction release; binary Eq result value; seen release;
        ]
        (acquire @ [ assign result contents ]);
      procedure "get_acquire"
        ([ executing; lower_bound; address ]
        @ implicit_state
        @ [ ghost ~implicit:true "q" real ])
        [ formal "result" value_type ]
        (common_pre fraction @ [ positive; binary Subseteq (variable "lower") release ])
        [
          context;
          ownership value fraction release;
          binary Eq result value;
          seen release;
          seen (variable "lower");
          binary Subseteq (variable "lower") release;
        ]
        [
          assign result (call "get" [ owner; location; value; release; fraction ]);
          R.Stmt.call ~loc (call "visibility_weaken" [ owner; release; variable "lower" ]);
        ];
      procedure "set"
        ([ executing; previous; address; formal "new_value" value_type ] @ implicit_state)
        [ release_output ]
        (common_pre one @ [ seen prior; holds new_value ])
        (write_post new_value) (write_body new_value);
      procedure "exchange"
        ([ executing; previous; address; formal "new_value" value_type ] @ implicit_state)
        [ formal "result" value_type; release_output ]
        (common_pre one @ [ seen prior; holds new_value ])
        (write_post new_value @ [ binary Eq result value ])
        ([ assign result contents ] @ write_body new_value);
      procedure "compare_and_set_acquire"
        ([
           executing;
           lower_bound;
           address;
           formal "exact" boolean;
           formal "old_value" value_type;
           formal "new_value" value_type;
         ]
        @ implicit_state
        @ [ ghost ~implicit:true "q" real ])
        [ formal "result" boolean; release_output ]
        (common_pre fraction
        @ [
            holds new_value;
            R.Expr.ite ~loc same (binary Eq fraction one) positive;
            binary Subseteq (variable "lower") release;
          ])
        [
          context;
          ownership changed_value fraction published;
          seen release;
          seen (variable "lower");
          binary Subseteq (variable "lower") published;
          binary Impl exact (binary Iff result same);
          binary Impl result same;
        ]
        (R.Stmt.local ~loc ~ghost:true ~typ:view_type
           ~init:(R.Stmt.expr_rhs (call "visibility_snapshot" [ owner ]))
           (ident "prior")
        @ [
            R.Stmt.assign ~loc [ result; published ]
              (R.Stmt.expr_rhs
                 (call "compare_and_set"
                    [
                      owner;
                      prior;
                      location;
                      exact;
                      old_value;
                      new_value;
                      value;
                      release;
                      fraction;
                    ]));
            R.Stmt.call ~loc
              (call "visibility_weaken" [ owner; release; variable "lower" ]);
          ]);
      procedure "compare_and_set"
        ([
           executing;
           previous;
           address;
           formal "exact" boolean;
           formal "old_value" value_type;
           formal "new_value" value_type;
         ]
        @ implicit_state
        @ [ ghost ~implicit:true "q" real ])
        [ formal "result" boolean; release_output ]
        (common_pre fraction
        @ [
            seen prior;
            holds new_value;
            R.Expr.ite ~loc same (binary Eq fraction one) positive;
          ])
        [
          context;
          ownership changed_value fraction published;
          seen release;
          seen prior;
          binary Impl result (binary Subseteq prior published);
          binary Impl exact (binary Iff result same);
          binary Impl result same;
          binary Impl result (binary Subseteq release published);
          binary Impl (R.Expr.not_ ~loc result) (binary Eq published release);
        ]
        (acquire_prior
        @ R.Stmt.local ~loc ~const:true ~typ:value_type ~init:(R.Stmt.expr_rhs contents)
            (ident "current")
        @ R.Stmt.local ~loc ~typ:boolean (ident "choice")
        @ [
            R.Stmt.havoc ~loc (name "choice");
            R.Stmt.if_ ~loc
              (binary And
                 (binary Eq (variable "current") old_value)
                 (binary Or exact (variable "choice")))
              [
                assign contents new_value;
                assign metadata acquired;
                assign published acquired;
                assign result (R.Expr.bool ~loc true);
              ]
              [ assign published release; assign result (R.Expr.bool ~loc false) ];
          ]);
    ]

let interface_members ~loc () =
  [
    R.Member.module_ ~loc ~interface:true
      ~params:[ (R.Ident.make ~loc "V", R.Name.make ~loc Prelude.value_interface) ]
      (R.Ident.make ~loc "AtomicSignature")
      (members ~loc ~implementation:false);
    R.Member.instance ~loc (R.Ident.make ~loc "Atomic")
      (R.Name.make ~loc "AtomicSignature");
  ]

let implementation_members ~loc () =
  [
    R.Member.module_ ~loc
      ~params:[ (R.Ident.make ~loc "V", R.Name.make ~loc Prelude.value_interface) ]
      ~implements:
        [
          ( R.Name.make ~loc "AtomicSignature",
            [ R.Type.named ~loc (R.Name.make ~loc "V") [] ] );
        ]
      (R.Ident.make ~loc "Atomic")
      (members ~loc ~implementation:true);
  ]
