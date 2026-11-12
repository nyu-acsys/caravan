(** One hidden visibility authority for each executing identity. *)

open Base
module R = Raven_api

let ident ~loc text = R.Ident.make ~loc text
let local ~loc text = R.Name.make ~loc text
let variable ~loc text = R.Expr.var ~loc (local ~loc text)
let view_type ~loc = R.Type.set ~loc (R.Type.ref ~loc)
let empty_view ~loc = R.Expr.annotated (R.Expr.set ~loc []) (view_type ~loc)

let call ~loc ~module_name text arguments =
  R.Expr.call ~loc (R.Name.make ~loc ~path:[ module_name ] text) arguments

let context ~loc ~module_name owner =
  call ~loc ~module_name "visibility_context" [ owner ]

let seen ~loc ~module_name owner lower =
  call ~loc ~module_name "visibility_seen" [ owner; lower ]

let snapshot ~loc ~module_name owner =
  call ~loc ~module_name "visibility_snapshot" [ owner ]

let reconcile ~loc ~module_name owner lower =
  call ~loc ~module_name "visibility_reconcile" [ owner; lower ]

let duplicate ~loc ~module_name owner lower =
  call ~loc ~module_name "visibility_duplicate" [ owner; lower ]

let weaken ~loc ~module_name owner larger lower =
  call ~loc ~module_name "visibility_weaken" [ owner; larger; lower ]

let handoff ~loc ~module_name source target =
  call ~loc ~module_name "visibility_handoff" [ source; target ]

let transfer ~loc ~module_name source target lower =
  call ~loc ~module_name "visibility_transfer" [ source; target; lower ]

let end_handoff ~loc ~module_name source target =
  call ~loc ~module_name "visibility_end_handoff" [ source; target ]

let begin_handoff ~loc source target =
  R.Expr.call ~loc (local ~loc "visibility_begin_handoff") [ source; target ]

let chunk ~loc kind view =
  let entries =
    R.Expr.call ~loc (R.Name.make ~loc ~path:[ "VisibilityViews" ] "set") [ view ]
  in
  R.Expr.call ~loc (R.Name.make ~loc ~path:[ "VisibilityAuthority" ] kind) [ entries ]

(** Authority growth is private to implementations with a justified acquisition. *)
let acquire ~loc ?prior owner incoming =
  let method_, arguments =
    match prior with
    | None -> ("visibility_acquire", [ owner; incoming ])
    | Some prior -> ("visibility_acquire_release", [ owner; prior; incoming ])
  in
  R.Expr.call ~loc (local ~loc method_) arguments

let publish ~loc owner prior =
  R.Expr.call ~loc (local ~loc "visibility_reconcile") [ owner; prior ]

let initial_field ~loc () =
  (local ~loc "visibility_frontier", Some (chunk ~loc "full" (empty_view ~loc)))

let fold_initial ~loc owner =
  R.Stmt.fold ~loc
    ~witnesses:[ (ident ~loc "view", empty_view ~loc) ]
    (local ~loc "visibility_context")
    [ owner ]

let members ~loc ~implementation =
  let reference text = R.Var.make ~loc ~ghost:true (ident ~loc text) (R.Type.ref ~loc) in
  let view_parameter text =
    R.Var.make ~loc ~ghost:true (ident ~loc text) (view_type ~loc)
  in
  let owner = variable ~loc "owner" in
  let lower = variable ~loc "lower" in
  let current = variable ~loc "current" in
  let view = variable ~loc "view" in
  let context = R.Expr.call ~loc (local ~loc "visibility_context") [ owner ] in
  let seen lower = R.Expr.call ~loc (local ~loc "visibility_seen") [ owner; lower ] in
  let own kind view =
    R.Expr.own ~loc
      [ R.Expr.field ~loc owner (local ~loc "visibility_frontier"); chunk ~loc kind view ]
  in
  let conjunction left right = R.Expr.binary ~loc And left right in
  let body contents = if implementation then Some contents else None in
  let predicate text formals contents =
    R.Member.callable
      (R.Callable.func ~loc ~kind:Pred ~formals (ident ~loc text) (body contents))
  in
  let lemma text formals returns requires ensures contents =
    R.Member.callable
      (R.Callable.proc ~loc ~kind:Lemma ~formals ~returns
         ~requires:(List.map requires ~f:R.Spec.make)
         ~ensures:(List.map ensures ~f:R.Spec.make)
         ~opens:(loc, []) (ident ~loc text) (body contents))
  in
  let reveal_current =
    R.Stmt.local ~loc ~ghost:true ~typ:(view_type ~loc) (ident ~loc "view")
    @ [
        R.Stmt.unfold ~loc
          ~witnesses:[ (ident ~loc "view", view) ]
          (local ~loc "visibility_context")
          [ owner ];
      ]
  in
  let fold_current =
    R.Stmt.fold ~loc
      ~witnesses:[ (ident ~loc "view", view) ]
      (local ~loc "visibility_context")
      [ owner ]
  in
  let acquisition ~prior:with_prior text =
    let incoming = variable ~loc "incoming" in
    let prior = variable ~loc "prior" in
    let advanced = R.Expr.binary ~loc Union view incoming in
    lemma text
      ([ reference "owner" ]
      @ (if with_prior then [ view_parameter "prior" ] else [])
      @ [ view_parameter "incoming" ])
      [ view_parameter "current" ]
      (context :: (if with_prior then [ seen prior ] else []))
      ([
         context;
         seen incoming;
         seen current;
         R.Expr.binary ~loc Subseteq incoming current;
       ]
      @
      if with_prior then [ seen prior; R.Expr.binary ~loc Subseteq prior current ] else []
      )
      (reveal_current
      @ (if with_prior then
           [
             R.Stmt.unfold ~loc (local ~loc "visibility_seen") [ owner; prior ];
             R.Stmt.assert_ ~loc (R.Spec.make (R.Expr.binary ~loc Subseteq prior view));
           ]
         else [])
      @ [
          R.Stmt.call ~loc
            (R.Expr.call ~loc (local ~loc "fpu")
               [
                 R.Expr.field ~loc owner (local ~loc "visibility_frontier");
                 chunk ~loc "full" view;
                 chunk ~loc "full" advanced;
               ]);
          R.Stmt.assign ~loc [ current ] (R.Stmt.expr_rhs advanced);
          R.Stmt.fold ~loc
            ~witnesses:[ (ident ~loc "view", current) ]
            (local ~loc "visibility_context")
            [ owner ];
          R.Stmt.fold ~loc (local ~loc "visibility_seen") [ owner; incoming ];
          R.Stmt.fold ~loc (local ~loc "visibility_seen") [ owner; current ];
        ]
      @
      if with_prior then
        [ R.Stmt.fold ~loc (local ~loc "visibility_seen") [ owner; prior ] ]
      else [])
  in
  let source = variable ~loc "source" in
  let target = variable ~loc "target" in
  let source_view = variable ~loc "source_view" in
  let target_view = variable ~loc "target_view" in
  let invocation text arguments = R.Expr.call ~loc (local ~loc text) arguments in
  let at_owner kind owner view =
    R.Expr.own ~loc
      [ R.Expr.field ~loc owner (local ~loc "visibility_frontier"); chunk ~loc kind view ]
  in
  let handoff = invocation "visibility_handoff" [ source; target ] in
  let subset = R.Expr.binary ~loc Subseteq source_view target_view in
  let handoff_witnesses =
    [ (ident ~loc "source_view", source_view); (ident ~loc "target_view", target_view) ]
  in
  let handoff_locals =
    List.concat_map [ "source_view"; "target_view" ] ~f:(fun text ->
        R.Stmt.local ~loc ~ghost:true ~typ:(view_type ~loc) (ident ~loc text))
  in
  let open_handoff =
    R.Stmt.unfold ~loc ~witnesses:handoff_witnesses
      (local ~loc "visibility_handoff")
      [ source; target ]
  in
  let close_handoff =
    R.Stmt.fold ~loc ~witnesses:handoff_witnesses
      (local ~loc "visibility_handoff")
      [ source; target ]
  in
  let fold_context owner view =
    R.Stmt.fold ~loc
      ~witnesses:[ (ident ~loc "view", view) ]
      (local ~loc "visibility_context")
      [ owner ]
  in
  let handoff_members =
    [
      predicate "visibility_handoff"
        [ reference "source"; reference "target" ]
        (R.Expr.exists ~loc
           [
             R.Var.make ~loc (ident ~loc "source_view") (view_type ~loc);
             R.Var.make ~loc (ident ~loc "target_view") (view_type ~loc);
           ]
           (conjunction
              (at_owner "full" source source_view)
              (conjunction (at_owner "full" target target_view) subset)));
      lemma "visibility_transfer"
        [
          reference "source";
          reference "target";
          R.Var.make ~loc ~ghost:true (ident ~loc "lower") (view_type ~loc);
        ]
        []
        [ handoff; invocation "visibility_seen" [ source; lower ] ]
        [ handoff; invocation "visibility_seen" [ target; lower ] ]
        (handoff_locals
        @ [
            open_handoff;
            R.Stmt.unfold ~loc (local ~loc "visibility_seen") [ source; lower ];
            R.Stmt.assert_ ~loc
              (R.Spec.make (R.Expr.binary ~loc Subseteq lower source_view));
            R.Stmt.fold ~loc (local ~loc "visibility_seen") [ target; lower ];
            close_handoff;
          ]);
      lemma "visibility_end_handoff"
        [ reference "source"; reference "target" ]
        [] [ handoff ]
        [
          invocation "visibility_context" [ source ];
          invocation "visibility_context" [ target ];
        ]
        (handoff_locals
        @ [
            open_handoff; fold_context source source_view; fold_context target target_view;
          ]);
    ]
  in
  let begin_handoff_member =
    lemma "visibility_begin_handoff"
      [ reference "source"; reference "target" ]
      []
      [
        invocation "visibility_context" [ source ];
        invocation "visibility_context" [ target ];
      ]
      [ handoff ]
      (handoff_locals
      @ [
          R.Stmt.unfold ~loc
            ~witnesses:[ (ident ~loc "source_view", view) ]
            (local ~loc "visibility_context")
            [ source ];
        ]
      @ R.Stmt.local ~loc ~ghost:true ~typ:(view_type ~loc)
          ~init:(R.Stmt.expr_rhs (acquire ~loc target source_view))
          (ident ~loc "acquired")
      @ [
          R.Stmt.unfold ~loc
            ~witnesses:[ (ident ~loc "target_view", view) ]
            (local ~loc "visibility_context")
            [ target ];
          R.Stmt.unfold ~loc (local ~loc "visibility_seen") [ target; source_view ];
          R.Stmt.assert_ ~loc (R.Spec.make subset);
          close_handoff;
        ])
  in
  [
    predicate "visibility_context"
      [ reference "owner" ]
      (R.Expr.exists ~loc
         [ R.Var.make ~loc (ident ~loc "view") (view_type ~loc) ]
         (own "full" view));
    predicate "visibility_seen"
      [ reference "owner"; view_parameter "lower" ]
      (own "frag" lower);
    lemma "visibility_snapshot"
      [ reference "owner" ]
      [ view_parameter "current" ]
      [ context ]
      [ context; seen current ]
      (reveal_current
      @ [
          R.Stmt.assign ~loc [ current ] (R.Stmt.expr_rhs view);
          fold_current;
          R.Stmt.fold ~loc (local ~loc "visibility_seen") [ owner; current ];
        ]);
    lemma "visibility_duplicate"
      [ reference "owner"; view_parameter "lower" ]
      []
      [ seen lower ]
      [ conjunction (seen lower) (seen lower) ]
      [
        R.Stmt.unfold ~loc (local ~loc "visibility_seen") [ owner; lower ];
        R.Stmt.fold ~loc (local ~loc "visibility_seen") [ owner; lower ];
        R.Stmt.fold ~loc (local ~loc "visibility_seen") [ owner; lower ];
      ];
    lemma "visibility_weaken"
      [ reference "owner"; view_parameter "current"; view_parameter "lower" ]
      []
      [ seen current; R.Expr.binary ~loc Subseteq lower current ]
      [ seen current; seen lower ]
      [
        R.Stmt.unfold ~loc (local ~loc "visibility_seen") [ owner; current ];
        R.Stmt.fold ~loc (local ~loc "visibility_seen") [ owner; current ];
        R.Stmt.fold ~loc (local ~loc "visibility_seen") [ owner; lower ];
      ];
    lemma "visibility_reconcile"
      [ reference "owner"; view_parameter "lower" ]
      [ view_parameter "current" ]
      [ context; seen lower ]
      [ context; seen lower; seen current; R.Expr.binary ~loc Subseteq lower current ]
      (reveal_current
      @ [
          R.Stmt.unfold ~loc (local ~loc "visibility_seen") [ owner; lower ];
          R.Stmt.assert_ ~loc (R.Spec.make (R.Expr.binary ~loc Subseteq lower view));
          R.Stmt.assign ~loc [ current ] (R.Stmt.expr_rhs view);
          fold_current;
          R.Stmt.fold ~loc (local ~loc "visibility_seen") [ owner; lower ];
          R.Stmt.fold ~loc (local ~loc "visibility_seen") [ owner; current ];
        ]);
  ]
  @ handoff_members
  @ [
      lemma "visibility_checkpoint"
        [ reference "owner" ]
        [ reference "cut" ]
        [ context ]
        [
          context;
          seen (R.Expr.set ~loc [ variable ~loc "cut" ]);
          R.Expr.binary ~loc Neq (variable ~loc "cut") (R.Expr.null ~loc);
        ]
        ([
           R.Stmt.ghost_block ~loc
             [ R.Stmt.assign ~loc [ variable ~loc "cut" ] (R.Stmt.new_rhs []) ];
         ]
        @ R.Stmt.local ~loc ~ghost:true ~typ:(view_type ~loc)
            ~init:
              (R.Stmt.expr_rhs
                 (acquire ~loc owner (R.Expr.set ~loc [ variable ~loc "cut" ])))
            (ident ~loc "checkpoint_view"));
    ]
  @
  if implementation then
    [
      begin_handoff_member;
      acquisition ~prior:false "visibility_acquire";
      acquisition ~prior:true "visibility_acquire_release";
    ]
  else []

let interface_members ~loc () = members ~loc ~implementation:false

let implementation_members ~loc () =
  let library text = R.Name.make ~loc ~path:[ "Library" ] text in
  [
    R.Member.instance ~loc
      ~def:(library "SetRA", [ R.Type.ref ~loc ])
      (ident ~loc "VisibilityViews")
      (library "SetRA");
    R.Member.instance ~loc
      ~def:(library "Auth", [ R.Type.named ~loc (local ~loc "VisibilityViews") [] ])
      (ident ~loc "VisibilityAuthority")
      (library "Auth");
    R.Member.field ~loc ~ghost:true
      (ident ~loc "visibility_frontier")
      (R.Type.named ~loc (local ~loc "VisibilityAuthority") []);
  ]
  @ members ~loc ~implementation:true
