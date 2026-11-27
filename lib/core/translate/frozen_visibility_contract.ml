(** Checked private writes and sealing of ordinary fields that become immutable. *)

open Base
module R = Raven_api

let initial_fields ~loc ~family ~owner ~event =
  let member text =
    Qualified_name.raven ~loc (Qualified_name.of_string (family ^ "." ^ text))
  in
  [
    (member "writer", Some owner);
    (member "seal", Some (R.Expr.null ~loc));
    (member "last_event", Some event);
  ]

let members ~loc ~implementation =
  let ident text = R.Ident.make ~loc text in
  let name text = R.Name.make ~loc text in
  let variable text = R.Expr.var ~loc (name text) in
  let call text arguments = R.Expr.call ~loc (name text) arguments in
  let binary = R.Expr.binary ~loc in
  let conjunction = List.reduce_exn ~f:(binary And) in
  let value_name text = R.Name.make ~loc ~path:[ "V" ] text in
  let value_type = R.Type.named ~loc (value_name "Carrier") [] in
  let reference = R.Type.ref ~loc in
  let real = R.Type.real ~loc in
  let view_type = Visibility_contract.view_type ~loc in
  let formal text typ = R.Var.make ~loc (ident text) typ in
  let ghost ?(implicit = false) text typ =
    R.Var.make ~loc ~ghost:true ~implicit (ident text) typ
  in
  let owner = variable "owner" in
  let location = variable "location" in
  let value = variable "value" in
  let writer = variable "last_writer" in
  let fraction = variable "q" in
  let cut = variable "cut_point" in
  let event = variable "event" in
  let next_event = variable "next_event" in
  let result = variable "result" in
  let new_value = variable "new_value" in
  let singleton = R.Expr.set ~loc [ cut ] in
  let one = R.Expr.real ~loc 1.0 in
  let field text = R.Expr.field ~loc location (name text) in
  let raw_ownership value fraction writer seal event =
    conjunction
      [
        R.Expr.own ~loc [ field "contents"; value; fraction ];
        R.Expr.own ~loc [ field "writer"; writer; fraction ];
        R.Expr.own ~loc [ field "seal"; seal; fraction ];
        R.Expr.own ~loc [ field "last_event"; event; fraction ];
      ]
  in
  let ownership_at value fraction writer event =
    call "ownership" [ location; value; fraction; writer; event ]
  in
  let ownership value fraction writer = ownership_at value fraction writer event in
  let seen_event writer = call "visibility_seen" [ writer; R.Expr.set ~loc [ event ] ] in
  let context = call "visibility_context" [ owner ] in
  let seen = call "visibility_seen" [ owner; singleton ] in
  let frozen = call "frozen" [ location; value; cut ] in
  let holds value = R.Expr.call ~loc (value_name "holds") [ value ] in
  let body statements = if implementation then Some statements else None in
  let assign target expression =
    R.Stmt.assign ~loc [ target ] (R.Stmt.expr_rhs expression)
  in
  let procedure ?(kind = R.Callable.Proc) ?(opens = []) text arguments returns requires
      ensures statements =
    R.Member.callable
      (R.Callable.proc ~loc ~kind ~formals:arguments ~returns
         ~requires:(List.map requires ~f:R.Spec.make)
         ~ensures:(List.map ensures ~f:R.Spec.make)
         ~opens:(loc, opens) (ident text) (body statements))
  in
  let executing = ghost "owner" reference in
  let address = formal "location" reference in
  let implicit_value = ghost ~implicit:true "value" value_type in
  let implicit_cut = ghost ~implicit:true "cut_point" reference in
  let implicit_writer = ghost ~implicit:true "last_writer" reference in
  let implicit_event = ghost ~implicit:true "event" reference in
  let positive = binary Gt fraction (R.Expr.real ~loc 0.0) in
  let checkpoint =
    R.Stmt.local ~loc ~ghost:true ~typ:reference
      ~init:(R.Stmt.expr_rhs (call "visibility_checkpoint" [ owner ]))
      (ident "next_event")
  in
  let released_view = variable "released_view" in
  let lower = variable "lower" in
  let seen_view view = call "visibility_seen" [ owner; view ] in
  let storage =
    if implementation then []
    else
      [
        R.Member.field ~loc ~where:(value_name "holds") (ident "contents") value_type;
        R.Member.field ~loc ~ghost:true (ident "writer") reference;
        R.Member.field ~loc ~ghost:true (ident "seal") reference;
        R.Member.field ~loc ~ghost:true (ident "last_event") reference;
        R.Member.callable
          (R.Callable.func ~loc ~kind:Pred ~inline:true
             ~formals:
               [
                 address;
                 ghost "value" value_type;
                 ghost "q" real;
                 ghost "last_writer" reference;
               ]
             ~returns:[ implicit_event ] (ident "ownership")
             (Some
                (binary And
                   (raw_ownership value fraction writer (R.Expr.null ~loc) event)
                   (R.Expr.ite ~loc positive
                      (binary And
                         (binary Neq event (R.Expr.null ~loc))
                         (seen_event writer))
                      (binary Eq event (R.Expr.null ~loc))))));
      ]
  in
  storage
  @ [
      (* A frozen field's invariant owns only the field's cells. *)
      R.Member.callable
        (R.Callable.func ~loc ~kind:Inv ~formals:[ address ]
           ~returns:[ implicit_value; ghost ~implicit:true "cut_point" reference ]
           ?depends:(Option.some_if (not implementation) (loc, []))
           (ident "frozen")
           (if implementation then
              Some
                (R.Expr.exists ~loc
                   [ formal "last_writer" reference ]
                   (raw_ownership value one writer cut cut))
            else None));
      procedure "make"
        [ executing; formal "new_value" value_type ]
        [ address ]
        [ context; holds new_value ]
        [
          context;
          R.Expr.exists ~loc [ formal "event" reference ] (ownership new_value one owner);
        ]
        (checkpoint
        @ [
            R.Stmt.assign ~loc [ location ]
              (R.Stmt.new_rhs
                 [
                   (name "contents", Some new_value);
                   (name "writer", Some owner);
                   (name "seal", Some (R.Expr.null ~loc));
                   (name "last_event", Some next_event);
                 ]);
          ]);
      procedure "write"
        [
          executing;
          address;
          formal "new_value" value_type;
          implicit_value;
          implicit_writer;
          implicit_event;
        ]
        []
        [
          context;
          ownership value one writer;
          holds new_value;
          R.Expr.ite ~loc (binary Eq writer owner) (R.Expr.bool ~loc true)
            (seen_event owner);
        ]
        [
          context;
          R.Expr.exists ~loc [ formal "event" reference ] (ownership new_value one owner);
        ]
        (checkpoint
        @ [
            assign (field "contents") new_value;
            assign (field "writer") owner;
            assign (field "last_event") next_event;
          ]);
      procedure "read_private"
        [
          executing;
          address;
          implicit_value;
          ghost ~implicit:true "q" real;
          implicit_event;
        ]
        [ formal "result" value_type ]
        [
          context;
          ownership value fraction owner;
          binary Gt fraction (R.Expr.real ~loc 0.0);
        ]
        [ context; ownership value fraction owner; binary Eq result value ]
        [ assign result (field "contents") ];
      procedure ~kind:Lemma "freeze"
        [ executing; address; implicit_value; implicit_event ]
        [ ghost ~implicit:true "cut_point" reference ]
        [ context; ownership value one owner ]
        [ context; frozen; seen; binary Eq cut event ]
        [
          assign cut event;
          assign (field "seal") event;
          R.Stmt.fold ~loc
            ~witnesses:[ (ident "last_writer", owner) ]
            (name "frozen") [ location; value; event ];
        ];
      procedure ~kind:Lemma "snapshot"
        [
          address;
          ghost "selected" (R.Type.bool ~loc);
          implicit_value;
          ghost ~implicit:true "q" real;
          implicit_writer;
          implicit_event;
        ]
        [ ghost "stamp" reference ]
        [ variable "selected"; ownership value fraction writer ]
        [
          variable "selected";
          ownership value fraction writer;
          binary Eq (variable "stamp") event;
        ]
        [ assign (variable "stamp") event ];
      procedure ~kind:Lemma "split"
        [
          address;
          ghost "selected" (R.Type.bool ~loc);
          implicit_value;
          ghost ~implicit:true "q" real;
          implicit_writer;
          implicit_event;
        ]
        []
        [ variable "selected"; positive; ownership value fraction writer ]
        [
          variable "selected";
          ownership value (binary Div fraction (R.Expr.real ~loc 2.0)) writer;
          ownership value (binary Div fraction (R.Expr.real ~loc 2.0)) writer;
        ]
        [
          R.Stmt.call ~loc
            (call "visibility_duplicate" [ writer; R.Expr.set ~loc [ event ] ]);
        ];
      procedure ~kind:Lemma "release_private"
        [
          executing;
          address;
          ghost "selected" (R.Type.bool ~loc);
          implicit_value;
          implicit_event;
        ]
        [ ghost "released_view" view_type ]
        [ context; variable "selected"; ownership value one owner ]
        [
          context;
          variable "selected";
          ownership value one owner;
          seen_view released_view;
          binary In event released_view;
        ]
        [
          assign released_view
            (call "visibility_reconcile" [ owner; R.Expr.set ~loc [ event ] ]);
        ];
      procedure ~kind:Lemma "adopt"
        [
          executing;
          address;
          ghost "selected" (R.Type.bool ~loc);
          ghost "lower" view_type;
          implicit_value;
          implicit_writer;
          implicit_event;
        ]
        []
        [
          context;
          variable "selected";
          ownership value one writer;
          seen_view lower;
          binary In event lower;
        ]
        [
          context;
          variable "selected";
          ownership value one owner;
          seen_view lower;
          binary In event lower;
        ]
        [
          R.Stmt.call ~loc
            (call "visibility_weaken" [ owner; lower; R.Expr.set ~loc [ event ] ]);
          assign (field "writer") owner;
        ];
      procedure ~kind:Lemma "transfer"
        [
          ghost "source" reference;
          ghost "target" reference;
          address;
          ghost "selected" (R.Type.bool ~loc);
          ghost "value" value_type;
          implicit_cut;
        ]
        []
        [
          variable "selected";
          frozen;
          call "visibility_handoff" [ variable "source"; variable "target" ];
          call "visibility_seen" [ variable "source"; singleton ];
        ]
        [
          variable "selected";
          frozen;
          call "visibility_handoff" [ variable "source"; variable "target" ];
          call "visibility_seen" [ variable "source"; singleton ];
          call "visibility_seen" [ variable "target"; singleton ];
        ]
        [
          R.Stmt.call ~loc (call "visibility_duplicate" [ variable "source"; singleton ]);
          R.Stmt.call ~loc
            (call "visibility_transfer"
               [ variable "source"; variable "target"; singleton ]);
        ];
      procedure ~kind:Lemma "freeze_owned"
        [
          executing;
          address;
          ghost "selected" (R.Type.bool ~loc);
          implicit_value;
          implicit_event;
        ]
        []
        [ context; variable "selected"; ownership value one owner ]
        [ context; call "frozen" [ location; value; event ]; seen_event owner ]
        (R.Stmt.local ~loc ~ghost:true ~typ:reference (ident "cut_point")
        @ [ assign cut (call "freeze" [ owner; location; value; event ]) ]);
      procedure ~kind:Lemma "release"
        [
          executing;
          address;
          ghost "selected" (R.Type.bool ~loc);
          implicit_value;
          implicit_cut;
        ]
        [ ghost "released_view" view_type ]
        [ context; variable "selected"; frozen; seen ]
        [ context; frozen; seen; seen_view released_view; binary In cut released_view ]
        [ assign released_view (Visibility_contract.publish ~loc owner singleton) ];
      procedure ~kind:Lemma "observe"
        [
          executing;
          address;
          ghost "selected" (R.Type.bool ~loc);
          ghost "lower" view_type;
          implicit_value;
          implicit_cut;
        ]
        []
        [ context; variable "selected"; frozen; seen_view lower; binary In cut lower ]
        [ context; frozen; seen; seen_view lower; binary In cut lower ]
        [ R.Stmt.call ~loc (call "visibility_weaken" [ owner; lower; singleton ]) ];
      procedure
        ~opens:[ (name "frozen", [ location ]) ]
        "read_frozen"
        [ executing; address; implicit_value; ghost ~implicit:true "cut_point" reference ]
        [ formal "result" value_type ]
        [ context; frozen; seen ]
        [ context; frozen; seen; binary Eq result value; holds result ]
        (R.Stmt.local ~loc ~ghost:true ~typ:reference (ident "last_writer")
        @ [
            R.Stmt.atomic_block ~loc
              [
                R.Stmt.unfold ~loc
                  ~witnesses:[ (ident "last_writer", writer) ]
                  (name "frozen") [ location; value; cut ];
                assign result (field "contents");
                R.Stmt.fold ~loc
                  ~witnesses:[ (ident "last_writer", writer) ]
                  (name "frozen") [ location; value; cut ];
              ];
          ]);
    ]

let parameters ~loc =
  [
    (R.Ident.make ~loc "Tag", R.Name.make ~loc ~path:[ "Library" ] "Type");
    (R.Ident.make ~loc "V", R.Name.make ~loc Prelude.value_interface);
  ]

let interface_members ~loc () =
  [
    R.Member.module_ ~loc ~interface:true ~params:(parameters ~loc)
      (R.Ident.make ~loc "FrozenSignature")
      (members ~loc ~implementation:false);
    R.Member.instance ~loc (R.Ident.make ~loc "Frozen")
      (R.Name.make ~loc "FrozenSignature");
  ]

let implementation_members ~loc () =
  [
    R.Member.module_ ~loc ~params:(parameters ~loc)
      ~implements:
        [
          ( R.Name.make ~loc "FrozenSignature",
            List.map [ "Tag"; "V" ] ~f:(fun text ->
                R.Type.named ~loc (R.Name.make ~loc text) []) );
        ]
      (R.Ident.make ~loc "Frozen")
      (members ~loc ~implementation:true);
  ]
