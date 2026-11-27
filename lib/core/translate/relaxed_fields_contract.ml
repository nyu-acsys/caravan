(** Past-write observations for explicitly relaxed ordinary fields. *)

open Base
module R = Raven_api

let module_name = "Caravan$RelaxedField"

let initial_fields ~loc ~family ~value ~event ~owner =
  let member text =
    Qualified_name.raven ~loc (Qualified_name.of_string (family ^ "." ^ text))
  in
  let entry = R.Expr.tuple ~loc [ event; value ] in
  [
    (member "last_event", Some event);
    (member "published_entries", Some (R.Expr.set ~loc []));
    ( member "publication",
      Some
        (R.Expr.call ~loc (member "CutAuth.auth")
           [ R.Expr.var ~loc (member "CutAgree.id") ]) );
    (member "private_owner", Some (R.Expr.tuple ~loc [ R.Expr.bool ~loc true; owner ]));
    ( member "writes",
      Some
        (R.Expr.call ~loc (member "Journal.auth")
           [ R.Expr.call ~loc (member "Entries.set") [ R.Expr.set ~loc [ entry ] ] ]) );
  ]

let support ~loc () =
  let ident text = R.Ident.make ~loc text in
  let name text = R.Name.make ~loc text in
  let variable text = R.Expr.var ~loc (name text) in
  let call text arguments = R.Expr.call ~loc (name text) arguments in
  let qualified owner text = R.Name.make ~loc ~path:[ owner ] text in
  let library text = qualified "Library" text in
  let binary = R.Expr.binary ~loc in
  let conjunction expressions = List.reduce_exn expressions ~f:(binary And) in
  let reference = R.Type.ref ~loc in
  let private_owner_type = R.Type.tuple ~loc [ R.Type.bool ~loc; reference ] in
  let value_type = R.Type.named ~loc (qualified "V" "Carrier") [] in
  let entry_type = R.Type.named ~loc (name "Entry") [] in
  let entries_type = R.Type.set ~loc entry_type in
  let formal ?(ghost = false) ?(implicit = false) text typ =
    R.Var.make ~loc ~ghost ~implicit (ident text) typ
  in
  let ghost ?(implicit = false) text typ = formal ~ghost:true ~implicit text typ in
  let location = variable "location" in
  let value = variable "value" in
  let event = variable "event" in
  let entries = variable "entries" in
  let published_entries = variable "published_entries" in
  let cut = variable "cut_point" in
  let private_owner = variable "private_owner" in
  let owner = variable "owner" in
  let null = R.Expr.null ~loc in
  let owned_owner = R.Expr.tuple ~loc [ R.Expr.bool ~loc true; owner ] in
  let invalid_owner = R.Expr.tuple ~loc [ R.Expr.bool ~loc false; null ] in
  let empty = R.Expr.annotated (R.Expr.set ~loc []) entries_type in
  let unpublished = binary Eq cut null in
  let context = Execution_contract.visibility_context ~loc owner in
  let visibility text args = Execution_contract.call ~loc text args in
  let seen owner event =
    visibility "visibility_seen" [ owner; R.Expr.set ~loc [ event ] ]
  in
  let published cut = call "published" [ location; cut ] in
  let result = variable "result" in
  let selected = variable "selected" in
  let next = variable "next" in
  let permitted = variable "permitted" in
  let guard = ghost "permitted" (R.Type.bool ~loc) in
  let new_value = variable "new_value" in
  let entry event value = R.Expr.tuple ~loc [ event; value ] in
  let singleton entry = R.Expr.set ~loc [ entry ] in
  let extended = binary Union entries (singleton (entry next new_value)) in
  let field text = R.Expr.field ~loc location (name text) in
  let chunk kind entries =
    R.Expr.call ~loc (qualified "Journal" kind)
      [ R.Expr.call ~loc (qualified "Entries" "set") [ entries ] ]
  in
  let cut_id = R.Expr.var ~loc (qualified "CutAgree" "id") in
  let agreement cut = R.Expr.call ~loc (qualified "CutAgree" "agree") [ cut ] in
  let cut_chunk kind value = R.Expr.call ~loc (qualified "CutAuth" kind) [ value ] in
  let cut_value = R.Expr.ite ~loc unpublished cut_id (agreement cut) in
  let authority entries = call "authority" [ location; entries ] in
  let observed event value = call "observed" [ location; event; value ] in
  let state_metadata value event entries published_entries cut private_owner =
    [ location; value; event; entries; published_entries; cut; private_owner ]
  in
  let state_with value event entries published_entries cut private_owner =
    call "state" (state_metadata value event entries published_entries cut private_owner)
  in
  let state value event entries =
    state_with value event entries published_entries cut private_owner
  in
  let state_arguments value event entries =
    state_metadata value event entries published_entries cut private_owner
  in
  let initial_state =
    state_with new_value next (singleton (entry next new_value)) empty null owned_owner
  in
  let extended_published =
    R.Expr.ite ~loc unpublished published_entries
      (binary Union published_entries (singleton (entry next new_value)))
  in
  (* The owner certifies an ordered private chain, rather than the last physical writer. *)
  let next_owner =
    R.Expr.ite ~loc (binary Eq private_owner owned_owner) owned_owner invalid_owner
  in
  let holds value = R.Expr.call ~loc (qualified "V" "holds") [ value ] in
  let stored entry = binary In entry entries in
  let predicate ?(kind = R.Callable.Pred) ?(inline = false) ?(returns = []) text formals
      body =
    R.Member.callable
      (R.Callable.func ~loc ~kind ~inline ~formals ~returns (ident text) (Some body))
  in
  let procedure ?(kind = R.Callable.Proc) ?(atomic = false) text formals returns requires
      ensures statements =
    R.Member.callable
      (R.Callable.proc ~loc ~kind ~atomic ~formals ~returns
         ~requires:(List.map requires ~f:R.Spec.make)
         ~ensures:(List.map ensures ~f:R.Spec.make)
         ~opens:(loc, []) (ident text) (Some statements))
  in
  let address = formal "location" reference in
  let executing = ghost "owner" reference in
  let implicit_state =
    [
      ghost ~implicit:true "value" value_type;
      ghost ~implicit:true "event" reference;
      ghost ~implicit:true "entries" entries_type;
      ghost ~implicit:true "published_entries" entries_type;
      ghost ~implicit:true "cut_point" reference;
      ghost ~implicit:true "private_owner" private_owner_type;
    ]
  in
  let assign target expression =
    R.Stmt.assign ~loc [ target ] (R.Stmt.expr_rhs expression)
  in
  let invoke expression = R.Stmt.call ~loc expression in
  let assert_ condition = R.Stmt.assert_ ~loc (R.Spec.make condition) in
  let update before after = invoke (call "fpu" [ field "writes"; before; after ]) in
  let fresh_event = [ assign next (visibility "visibility_checkpoint" [ owner ]) ] in
  let fold_state value event entries =
    R.Stmt.fold ~loc (name "state") (state_arguments value event entries)
  in
  let unfold_state =
    R.Stmt.unfold ~loc (name "state") (state_arguments value event entries)
  in
  let event_value = R.Expr.tuple_get ~loc (variable "entry") 1 in
  let legal =
    R.Expr.forall ~loc
      [ formal "entry" entry_type ]
      (binary Impl (stored (variable "entry")) (holds event_value))
  in
  let read ~published_only =
    let selection = if published_only then published_entries else entries in
    let membership = binary In (entry selected result) selection in
    let visible_cut = variable "visible_cut" in
    let visibility_contract =
      if published_only then [ context; published visible_cut; seen owner visible_cut ]
      else []
    in
    let visible_parameter =
      if published_only then [ ghost ~implicit:true "visible_cut" reference ] else []
    in
    let reconcile_cut =
      if published_only then
        [ assert_ (binary Eq cut visible_cut); assert_ (binary Neq cut null) ]
      else []
    in
    procedure ~atomic:true
      (if published_only then "read_published" else "read")
      ((if published_only then [ executing ] else [])
      @ [ address ] @ implicit_state @ visible_parameter)
      [ formal "result" value_type; ghost ~implicit:true "selected" reference ]
      (state value event entries :: visibility_contract)
      ([ state value event entries; observed selected result; membership; holds result ]
      @ visibility_contract)
      ([ unfold_state ] @ reconcile_cut
      @ [
          R.Stmt.havoc ~loc (name "result");
          R.Stmt.havoc ~loc (name "selected");
          R.Stmt.assume ~loc (R.Spec.make membership);
          invoke (call "remember" [ location; entries; selected; result ]);
          fold_state value event entries;
        ])
  in
  [
    R.Member.module_ ~loc
      ~params:[ (ident "Tag", library "Type"); (ident "V", name Prelude.value_interface) ]
      (ident module_name)
      [
        R.Member.module_ ~loc
          ~implements:[ (library "Type", []) ]
          (ident "Entry")
          [
            R.Member.type_ ~loc ~rep:true (ident "T")
              (Some (R.Type.tuple ~loc [ reference; value_type ]));
          ];
        R.Member.module_ ~loc
          ~implements:[ (library "Type", []) ]
          (ident "Cut")
          [ R.Member.type_ ~loc ~rep:true (ident "T") (Some reference) ];
        R.Member.instance ~loc
          ~def:(library "Agree", [ R.Type.named ~loc (name "Cut") [] ])
          (ident "CutAgree") (library "Agree");
        R.Member.instance ~loc
          ~def:(library "Auth", [ R.Type.named ~loc (name "CutAgree") [] ])
          (ident "CutAuth") (library "Auth");
        R.Member.instance ~loc
          ~def:(library "SetRA", [ entry_type ])
          (ident "Entries") (library "SetRA");
        R.Member.instance ~loc
          ~def:(library "Auth", [ R.Type.named ~loc (name "Entries") [] ])
          (ident "Journal") (library "Auth");
        R.Member.field ~loc ~where:(qualified "V" "holds") (ident "contents") value_type;
        R.Member.field ~loc ~ghost:true (ident "last_event") reference;
        R.Member.field ~loc ~ghost:true (ident "published_entries") entries_type;
        R.Member.field ~loc ~ghost:true (ident "publication")
          (R.Type.named ~loc (name "CutAuth") []);
        R.Member.field ~loc ~ghost:true (ident "private_owner") private_owner_type;
        predicate ~inline:true "published" [ address ]
          ~returns:[ ghost ~implicit:true "cut_point" reference ]
          (binary And (binary Neq cut null)
             (R.Expr.own ~loc [ field "publication"; cut_chunk "frag" (agreement cut) ]));
        R.Member.field ~loc ~ghost:true (ident "writes")
          (R.Type.named ~loc (name "Journal") []);
        predicate "authority"
          [ address; ghost "entries" entries_type ]
          (R.Expr.own ~loc [ field "writes"; chunk "auth" entries ]);
        predicate ~inline:true "observed"
          [ address; ghost "event" reference; ghost "value" value_type ]
          (R.Expr.own ~loc
             [ field "writes"; chunk "frag" (singleton (entry event value)) ]);
        predicate "state" [ address ] ~returns:implicit_state
          (conjunction
             [
               R.Expr.own ~loc [ field "contents"; value ];
               R.Expr.own ~loc [ field "last_event"; event ];
               authority entries;
               R.Expr.own ~loc [ field "published_entries"; published_entries ];
               R.Expr.own ~loc [ field "private_owner"; private_owner ];
               R.Expr.own ~loc [ field "publication"; cut_chunk "auth" cut_value ];
               binary Subseteq published_entries entries;
               R.Expr.ite ~loc unpublished
                 (binary Eq published_entries empty)
                 (binary In (entry event value) published_entries);
               stored (entry event value);
               binary Neq event null;
               legal;
             ]);
        procedure ~kind:Lemma "remember"
          [
            address;
            ghost "entries" entries_type;
            ghost "event" reference;
            ghost "value" value_type;
          ]
          []
          [ authority entries; stored (entry event value) ]
          [ authority entries; observed event value ]
          [
            R.Stmt.unfold ~loc (name "authority") [ location; entries ];
            update (chunk "auth" entries)
              (R.Expr.call ~loc
                 (qualified "Journal" "auth_frag")
                 [
                   R.Expr.call ~loc (qualified "Entries" "set") [ entries ];
                   R.Expr.call ~loc (qualified "Entries" "set")
                     [ singleton (entry event value) ];
                 ]);
            R.Stmt.fold ~loc (name "authority") [ location; entries ];
          ];
        procedure ~kind:Lemma "duplicate"
          [ address; guard; ghost "event" reference; ghost "value" value_type ]
          []
          [ permitted; observed event value ]
          [ permitted; observed event value; observed event value ]
          [];
        procedure ~kind:Lemma "reconcile"
          ([ address; guard; ghost "selected" reference; ghost "result" value_type ]
          @ implicit_state)
          []
          [ permitted; state value event entries; observed selected result ]
          [
            permitted;
            state value event entries;
            observed selected result;
            stored (entry selected result);
          ]
          [
            unfold_state;
            R.Stmt.unfold ~loc (name "authority") [ location; entries ];
            assert_ (stored (entry selected result));
            R.Stmt.fold ~loc (name "authority") [ location; entries ];
            fold_state value event entries;
          ];
        procedure ~kind:Lemma "snapshot"
          (address :: guard :: implicit_state)
          [ ghost "snapshot_event" reference; ghost "snapshot_entries" entries_type ]
          [ permitted; state value event entries ]
          [
            permitted;
            state value event entries;
            stored (entry (variable "snapshot_event") value);
            binary Eq (variable "snapshot_event") event;
            binary Eq (variable "snapshot_entries") entries;
          ]
          [
            unfold_state;
            assign (variable "snapshot_event") event;
            assign (variable "snapshot_entries") entries;
            fold_state value event entries;
          ];
        procedure ~kind:Lemma "observation"
          [
            address;
            guard;
            ghost "value" value_type;
            ghost ~implicit:true "event" reference;
          ]
          [ ghost "snapshot_event" reference ]
          [ permitted; observed event value ]
          [ permitted; observed event value; binary Eq (variable "snapshot_event") event ]
          [ assign (variable "snapshot_event") event ];
        procedure ~kind:Lemma "initialize"
          [ executing; address; ghost "new_value" value_type; ghost "next" reference ]
          []
          [
            holds new_value;
            binary Neq next null;
            R.Expr.own ~loc [ field "publication"; cut_chunk "auth" cut_id ];
            R.Expr.own ~loc [ field "published_entries"; empty ];
            R.Expr.own ~loc [ field "private_owner"; owned_owner ];
            R.Expr.own ~loc [ field "contents"; new_value ];
            R.Expr.own ~loc [ field "last_event"; next ];
            R.Expr.own ~loc
              [ field "writes"; chunk "auth" (singleton (entry next new_value)) ];
          ]
          [ initial_state; observed next new_value ]
          [
            R.Stmt.fold ~loc (name "authority")
              [ location; singleton (entry next new_value) ];
            invoke
              (call "remember"
                 [ location; singleton (entry next new_value); next; new_value ]);
            R.Stmt.fold ~loc (name "state")
              (state_metadata new_value next
                 (singleton (entry next new_value))
                 empty null owned_owner);
          ];
        procedure "make"
          [ executing; formal "new_value" value_type ]
          [ address; ghost "next" reference ]
          [ context; holds new_value ]
          [ context; seen owner next; initial_state; observed next new_value ]
          (fresh_event
          @ [
              R.Stmt.assign ~loc [ location ]
                (R.Stmt.new_rhs
                   [
                     (name "contents", Some new_value);
                     (name "last_event", Some next);
                     (name "publication", Some (cut_chunk "auth" cut_id));
                     (name "published_entries", Some empty);
                     (name "private_owner", Some owned_owner);
                     ( name "writes",
                       Some (chunk "auth" (singleton (entry next new_value))) );
                   ]);
              invoke (call "initialize" [ owner; location; new_value; next ]);
            ]);
        read ~published_only:false;
        read ~published_only:true;
        procedure ~kind:Lemma "adopt"
          (executing :: address :: guard :: implicit_state)
          []
          [
            permitted;
            context;
            state value event entries;
            unpublished;
            R.Expr.tuple_get ~loc private_owner 0;
            seen owner event;
          ]
          [
            permitted;
            context;
            state_with value event entries published_entries cut owned_owner;
            unpublished;
            seen owner event;
          ]
          [
            unfold_state;
            assign (field "private_owner") owned_owner;
            R.Stmt.fold ~loc (name "state")
              (state_metadata value event entries published_entries cut owned_owner);
          ];
        procedure ~kind:Lemma "publish"
          (executing :: address :: guard :: implicit_state)
          [ ghost "publication_cut" reference ]
          [
            permitted;
            context;
            state value event entries;
            unpublished;
            binary Eq private_owner owned_owner;
            seen owner event;
          ]
          [
            permitted;
            context;
            seen owner event;
            state_with value event entries
              (singleton (entry event value))
              (variable "publication_cut") private_owner;
            published (variable "publication_cut");
            seen owner (variable "publication_cut");
            binary Eq (variable "publication_cut") event;
            binary Neq (variable "publication_cut") null;
          ]
          [
            unfold_state;
            assign (variable "publication_cut") event;
            invoke
              (visibility "visibility_duplicate" [ owner; R.Expr.set ~loc [ event ] ]);
            invoke
              (call "fpu"
                 [ field "publication"; cut_chunk "auth" cut_id; cut_chunk "full" cut_id ]);
            invoke
              (call "fpu"
                 [
                   field "publication";
                   cut_chunk "full" cut_id;
                   cut_chunk "full" (agreement (variable "publication_cut"));
                 ]);
            assign (field "published_entries") (singleton (entry event value));
            R.Stmt.fold ~loc (name "state")
              (state_metadata value event entries
                 (singleton (entry event value))
                 (variable "publication_cut") private_owner);
          ];
        procedure ~kind:Lemma "release"
          [ executing; address; guard; ghost ~implicit:true "cut_point" reference ]
          [ ghost "released_view" (Visibility_contract.view_type ~loc) ]
          [ permitted; context; published cut; seen owner cut ]
          [
            permitted;
            context;
            published cut;
            seen owner cut;
            visibility "visibility_seen" [ owner; variable "released_view" ];
            binary In cut (variable "released_view");
          ]
          [
            assign (variable "released_view")
              (visibility "visibility_reconcile" [ owner; R.Expr.set ~loc [ cut ] ]);
          ];
        procedure ~kind:Lemma "acquire"
          [
            executing;
            address;
            guard;
            ghost "lower" (Visibility_contract.view_type ~loc);
            ghost ~implicit:true "cut_point" reference;
          ]
          []
          [
            permitted;
            context;
            published cut;
            visibility "visibility_seen" [ owner; variable "lower" ];
            binary In cut (variable "lower");
          ]
          [
            permitted;
            context;
            published cut;
            seen owner cut;
            visibility "visibility_seen" [ owner; variable "lower" ];
            binary In cut (variable "lower");
          ]
          [
            invoke
              (visibility "visibility_weaken"
                 [ owner; variable "lower"; R.Expr.set ~loc [ cut ] ]);
          ];
        procedure ~kind:Lemma "transfer"
          [
            ghost "source" reference;
            ghost "target" reference;
            address;
            guard;
            ghost ~implicit:true "cut_point" reference;
          ]
          []
          [
            permitted;
            published cut;
            Execution_contract.visibility_handoff ~loc (variable "source")
              (variable "target");
            seen (variable "source") cut;
          ]
          [
            permitted;
            published cut;
            Execution_contract.visibility_handoff ~loc (variable "source")
              (variable "target");
            seen (variable "source") cut;
            seen (variable "target") cut;
          ]
          [
            invoke
              (visibility "visibility_duplicate"
                 [ variable "source"; R.Expr.set ~loc [ cut ] ]);
            invoke
              (Execution_contract.visibility_transfer ~loc (variable "source")
                 (variable "target") (R.Expr.set ~loc [ cut ]));
          ];
        procedure ~atomic:true "write"
          (executing :: address :: formal "new_value" value_type :: implicit_state)
          [ ghost ~implicit:true "next" reference ]
          [ context; state value event entries; holds new_value ]
          [
            context;
            seen owner next;
            state_with new_value next extended extended_published cut next_owner;
            observed next new_value;
          ]
          (fresh_event
          @ [
              unfold_state;
              R.Stmt.unfold ~loc (name "authority") [ location; entries ];
              update (chunk "auth" entries) (chunk "full" entries);
              update (chunk "full" entries) (chunk "full" extended);
              R.Stmt.fold ~loc (name "authority") [ location; extended ];
              invoke (call "remember" [ location; extended; next; new_value ]);
              assign (field "contents") new_value;
              assign (field "last_event") next;
              assign (field "published_entries") extended_published;
              assign (field "private_owner") next_owner;
              R.Stmt.fold ~loc (name "state")
                (state_metadata new_value next extended extended_published cut next_owner);
            ]);
      ];
  ]
