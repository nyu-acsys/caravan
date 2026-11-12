(**************************************************************************)
(*                                                                        *)
(*  GOSPEL -- A Specification Language for OCaml                          *)
(*                                                                        *)
(*  Copyright (c) 2018- The VOCaL Project                                 *)
(*                                                                        *)
(*  This software is free software, distributed under the MIT license     *)
(*  (as described in file LICENSE enclosed).                              *)
(**************************************************************************)

%{
  (* Gospel's grammar (uparser.mly of github.com/ocaml-gospel/gospel at ce26d16), for
     Caravan's contracts: Gospel's terms, patterns and types, with OCaml's match and list
     literals in place of Gospel's indexing, and a contract's header and clauses. *)

  open Spec_ast

  let mk_pid pid ?(fixity = Normal) l = mk_id pid ~fixity ~attrs:[] ~loc:(mk_loc l)
  let mk_term d l = { term_desc = d; term_loc = mk_loc l }
  let mk_pat p l = { pat_desc = p; pat_loc = mk_loc l }
  let mk_proof d l = { proof_desc = d; proof_loc = mk_loc l }

  let implicit_parameter kind (x, attribute, at, ty) =
    let x = match attribute with
      | None -> x
      | Some "implicit" -> add_attr x "implicit"
      | Some _ -> raise (Syntax_error (at,
          "Only [@implicit] is supported on " ^ kind ^ " parameters"))
    in (x, ty)

  let proof_value t = { proof_desc = Proof_value t; proof_loc = t.term_loc }

  let rec term_of_proof e =
    match e.proof_desc with
    | Proof_value t -> t
    | Proof_let (p, a, b) ->
        { term_desc = Tlet (p, term_of_proof a, term_of_proof b); term_loc = e.proof_loc }
    | Proof_if (c, a, b) ->
        { term_desc = Tif (c, term_of_proof a, term_of_proof b); term_loc = e.proof_loc }
    | Proof_match (t, cases) ->
        { term_desc = Tmatch (t, List.map (fun (p, body) -> p, term_of_proof body) cases);
          term_loc = e.proof_loc }
    | Proof_seq _ | Proof_assert _ | Proof_fold _ | Proof_unfold _ ->
        raise (Syntax_error (e.proof_loc,
          "A proof operation cannot occur in a logical expression"))

  let proof_term desc loc = proof_value (mk_term desc loc)

  (* A fold's or unfold's last argument, if a record, gives the witnesses. *)
  let record_argument t =
    match t.term_desc with
    | Tapply (f, { term_desc = Trecord (None, fields); _ }) -> (f, fields)
    | _ -> (t, [])

  let split_items items =
    ( List.filter_map (function `Decl d -> Some d | `Outline _ -> None) items,
      List.filter_map (function `Outline o -> Some o | `Decl _ -> None) items )

  (* The record types that no invariant takes as its state are logical records. *)
  let logical_records declarations =
    let rec states = function
      | Proof_invariant { inv_state = (_, PTtyapp (q, _)); _ } ->
          [ (match q with Qid x | Qdot (_, x) -> x.pid_str) ]
      | Proof_module { module_declarations = ds; _ }
      | Proof_definition { module_declarations = ds; _ } -> List.concat_map states ds
      | _ -> []
    in
    let states = List.concat_map states declarations in
    let field f =
      if f.sf_grows || f.sf_helps <> None then
        raise (Syntax_error (f.sf_name.pid_loc,
          "Only the state of an invariant has [@grows] or [@helps] fields"));
      (f.sf_name, f.sf_type)
    in
    let rec convert = function
      | Proof_state { state_name = n; state_params = ps; state_fields = fs }
        when not (List.mem n.pid_str states) ->
          Proof_type { type_name = n; type_params = ps; type_kind = Record (List.map field fs); type_recursive = true }
      | Proof_module m ->
          Proof_module { m with module_declarations = List.map convert m.module_declarations }
      | Proof_definition m ->
          Proof_definition
            { m with module_declarations = List.map convert m.module_declarations }
      | d -> d
    in
    List.map convert declarations

  (* An unfold's record names the existentials it binds, as in [{ root; head }]. *)
  let pun_name ~at (field, value) =
    match value.term_desc with
    | Tvar (Qid x) when x.pid_str = field.pid_str -> field
    | _ -> raise (Syntax_error (at, "An unfold names the existentials it binds"))

  let own_application f labels location value loc =
    begin match f.term_desc with
    | Tvar (Qid id) when id.pid_str = "own" -> ()
    | _ -> raise (Syntax_error (f.term_loc,
        "Only own accepts labeled arguments"))
    end;
    let add (fraction, writer, release) = function
      | `Fraction term when Option.is_none fraction -> (Some term, writer, release)
      | `Writer term when Option.is_none writer -> (fraction, Some term, release)
      | `Release term when Option.is_none release -> (fraction, writer, Some term)
      | `Fraction term | `Writer term | `Release term ->
          raise (Syntax_error (term.term_loc, "Duplicate labels on own"))
    in
    let fraction, writer, release = List.fold_left add (None, None, None) labels in
    begin match writer, release with
    | Some writer, Some release ->
        raise (Syntax_error (release.term_loc,
          "The ~writer and ~release labels cannot be used together on own"))
    | _ -> ()
    end;
    let full = mk_term (Tvar (Qdot (Qid (mk_pid "Permission" loc),
      mk_pid "full" loc))) loc in
    let args = match release with
      | Some release ->
          [location; value; Option.value fraction ~default:full; mk_term (Ttuple []) loc; release]
      | None -> [location; value; Option.value fraction ~default:full] @ Option.to_list writer
    in
    let apply f arg = mk_term (Tapply (f, arg)) loc in
    (List.fold_left apply f args).term_desc

  let add_clause c (keyword, t) =
    match keyword with
    | `Requires -> { c with requires = t :: c.requires }
    | `Ensures -> { c with ensures = t :: c.ensures }
    | `Atomic_requires -> { c with atomic_requires = t :: c.atomic_requires }
    | `Atomic_ensures -> { c with atomic_ensures = t :: c.atomic_ensures }
    | `Raises (p, post) -> { c with raises = (p, post) :: c.raises }
    | `Atomic_raises (p, post) -> { c with atomic_raises = (p, post) :: c.atomic_raises }
    | `Variant -> { c with variant = t :: c.variant }
    | `Pure -> { c with pure = true }
    | `Continues f -> { c with continues = Some f }

  let mk_contract header clauses =
    let atomic, header =
      match header with Some (atomic, h) -> (atomic, Some h) | None -> (false, None)
    in
    let c = List.fold_left add_clause { empty_contract with header; atomic } clauses in
    { c with requires = List.rev c.requires; ensures = List.rev c.ensures;
             atomic_requires = List.rev c.atomic_requires;
             atomic_ensures = List.rev c.atomic_ensures;
             raises = List.rev c.raises;
             atomic_raises = List.rev c.atomic_raises;
             variant = List.rev c.variant }
%}

(* Tokens *)

%token <string> LIDENT UIDENT
%token <string> OP1 OP2 OP3 OP4 OPPREF
%token <string> QUOTE_LIDENT
%token <string> BACKQUOTE_LIDENT
%token <string> POLY_TAG
%token <string> ATTRIBUTE

%token <string * char option> INTEGER
%token <string> FLOAT
%token <char> CHAR
%token <string> STRING

(* Contract tokens *)

%token REQUIRES ENSURES VARIANT OPENS PURE INVARIANT PREDICATE FOLD UNFOLD ASSERT ATOMIC
%token ATOMIC_REQUIRES ATOMIC_ENSURES ATOMIC_RAISES RAISES COMMIT RETURNING TYPE VIEW LEFTBRC RIGHTBRC
%token ACTION INITIALLY PERFORMS CONSUMES LINEARIZES LEADSTO CONTINUES WAIT ON HELPS AS PROOF AT
%token LEMMA RETURNS OF BEGIN END MODULE STRUCT FUN SET_OF_PREDICATE FRACTION WRITER RELEASE

(* Keywords *)

%token ELSE EXISTS FALSE FORALL IF IN LET REC NONREC MATCH NOT OLD THEN TRUE WITH

(* Symbols *)

%token CONJ AMPAMP ARROW BAR BARBAR COLON COLONCOLON COMMA DOT DOTDOT
%token EOF EQUAL
%token LRARROW LEFTPAR
%token LEFTSQ LTGT DISJ RIGHTPAR RIGHTSQ SEMICOLON
%token LEFTSQRIGHTSQ
%token STAR UNDERSCORE

(* Priorities *)

%nonassoc below_BAR
%left BAR
%nonassoc below_SEMICOLON
%right SEMICOLON
%nonassoc IN
%nonassoc DOT ELSE
%nonassoc prec_named
%right COLON

%right ARROW LRARROW
%right DISJ BARBAR
%right CONJ AMPAMP
%nonassoc NOT
%right EQUAL LTGT OP1
%right COLONCOLON
%left OP2
%left OP3 STAR
%left OP4
%left BACKQUOTE_LIDENT
%nonassoc prec_prefix_op
%nonassoc OPPREF
%nonassoc OLD

%start <Spec_ast.contract> contract
%start <Spec_ast.term> term_eof
%start <Spec_ast.proof_expr> proof_expr_eof
%start <Spec_ast.access_scope> scope
%start <Spec_ast.return_adapter> return_adapter
%start <Spec_ast.loop_spec> loop_spec
%start <Spec_ast.predicate> predicate
%start <Spec_ast.predicate> invariant_declaration
%start <Spec_ast.ghost_module> ghost_module_declaration
%start <Spec_ast.proof_file> proof
%start <Spec_ast.ghost_stmt list> ghost_stmts
%start <Spec_ast.linearization> linearization
%start <Spec_ast.initialization> initially
%%

ghost_module_declaration:
| MODULE name = uident COLON interface = uqualid EOF
    { { ghost_module_name = name; ghost_module_interface = interface } }
;

contract:
| h = header? cs = clause* EOF { mk_contract h cs }
;

term_eof:
| t = term EOF { t }
;

proof_expr_eof:
| e = proof_expr EOF { e }
;

scope:
| value = scope_expression EOF { value }
;

scope_expression:
| parent = uqualid DOT method_ = lident LEFTPAR FUN operation = lident state = pat_arg?
    ARROW body = proof_expr RIGHTPAR
    { let f = Qdot (parent, method_) in
      begin match f, state with
      | Qdot (Qid ghost, scope), None
        when ghost.pid_str = "Ghost" &&
          List.mem scope.pid_str ["scope"; "frozen_scope"; "published_scope"; "release_scope"; "acquire_scope"] -> ()
      | Qdot (Qdot (Qid ghost, state), scope), Some _
        when ghost.pid_str = "Ghost" && state.pid_str = "State"
          && List.mem scope.pid_str ["scope"; "frozen_scope"; "published_scope"; "release_scope"; "acquire_scope"] -> ()
      | _ -> raise (Syntax_error (mk_loc $loc(parent),
          "Expected a Ghost scope wrapper with one binder, or a Ghost.State scope wrapper with two binders"))
      end;
      let mode = match f with
        | Qdot (_, kind) -> begin match kind.pid_str with
            | "frozen_scope" -> Frozen_scope
            | "published_scope" -> Published_scope
            | "release_scope" -> Release_scope
            | "acquire_scope" -> Acquire_scope
            | _ -> General_scope end
        | _ -> General_scope in
      { scope_mode = mode; scope_operation = operation; scope_state = state; scope_body = body } }
;

return_adapter:
| adapter = return_adapter_expr EOF { adapter }
;

return_adapter_expr:
| ghost = uqualid DOT RETURNS LEFTPAR FUN result = pat_arg state = pat_arg
    ARROW body = proof_expr RIGHTPAR
    { if not (match ghost with Qid id -> id.pid_str = "Ghost" | Qdot _ -> false) then
        raise (Syntax_error (qualid_loc ghost, "Expected Ghost.returns"));
      { returns_result = result; returns_state = state; returns_body = body } }
;

loop_spec:
| cs = loop_clause* EOF
    { let invariants = List.filter_map (function
        | `Invariant t -> Some t
        | `State_invariant _ | `Variant _ | `Raises _ -> None) cs in
      let state_invariants = List.filter_map (function
        | `State_invariant invariant -> Some invariant
        | `Invariant _ | `Variant _ | `Raises _ -> None) cs in
      let loop_variant = List.filter_map (function
        | `Variant t -> Some t
        | `Invariant _ | `State_invariant _ | `Raises _ -> None) cs in
      let loop_raises = List.filter_map (function
        | `Raises clause -> Some clause
        | `Invariant _ | `State_invariant _ | `Variant _ -> None) cs in
      { invariants; state_invariants; loop_variant; loop_raises } }
;

predicate:
| p = predicate_decl EOF { p }
;

invariant_declaration:
| INVARIANT n = lident ps = predicate_param+ EOF
    { { pred_name = n; pred_params = ps; pred_body = None;
        pred_persistent = true; pred_inline = false } }
;

predicate_decl:
| PREDICATE a = ATTRIBUTE? n = lident ps = predicate_param+ t = preceded(EQUAL, term)?
    { let inline =
        match a with
        | None -> false
        | Some "inline" when t <> None -> true
        | Some "inline" ->
            raise (Syntax_error (n.pid_loc, "An inline predicate needs a body"))
        | Some _ ->
            raise (Syntax_error (mk_loc $loc(a), "A predicate's attribute is [@inline]"))
      in
      { pred_name = n; pred_params = ps; pred_body = t;
        pred_persistent = false; pred_inline = inline } }
;

(* The declarations of a proof file. *)
proof:
| items = proof_item* EOF
    { let declarations, outlines = split_items items in
      { declarations = logical_records declarations; outlines } }
;

proof_item:
| d = proof_decl { `Decl d }
| o = outline(outline_steps) { `Outline o }
;

outline(steps):
| PROOF n = lident COMMA rs = separated_nonempty_list(COMMA, ret_value)
    EQUAL b = outline_body(steps)
    { ignore rs;
      match b with
      | `Steps _ -> raise (Syntax_error (n.pid_loc, "Ghost results are followed by = and the call"))
      | `Contract (f, fs, contract_end, ss) ->
          let params = List.filter_map (function Lvar x -> Some x | _ -> None) fs in
          { outline_name = f; outline_params = (if params = [] then None else Some params);
            outline_contract = Option.map (fun e ->
              { (mk_loc $loc) with loc_start = $startpos(n); loc_end = e }) contract_end;
            outline_steps = ss; outline_loc = mk_loc $loc } }
| PROOF n = lident ps = fun_arg* cs = outline_clause* EQUAL b = outline_body(steps)
    { let params ps =
        match List.filter_map (function Lvar x -> Some x | _ -> None) ps with
        | [] -> None
        | xs -> Some xs
      in
      let header_end = match cs with [] -> None | _ -> Some $endpos(cs) in
      match b with
      | `Steps ss ->
          { outline_name = n; outline_params = params ps;
            outline_contract =
              Option.map (fun e -> { (mk_loc $loc) with loc_start = $startpos(n); loc_end = e })
                header_end;
            outline_steps = ss; outline_loc = mk_loc $loc }
      | `Contract (f, fs, contract_end, ss) ->
          if ps <> [] || cs <> [] then
            raise (Syntax_error (n.pid_loc, "A result name is followed by = and the call"));
          { outline_name = f; outline_params = params fs;
            outline_contract =
              Option.map (fun e -> { (mk_loc $loc) with loc_start = $startpos(n); loc_end = e })
                contract_end;
            outline_steps = ss; outline_loc = mk_loc $loc } }
;

outline_body(steps):
| ss = steps { `Steps ss }
| f = lident fs = fun_arg* cs = outline_clause* EQUAL ss = steps
    { `Contract (f, fs, (match cs with [] -> None | _ -> Some $endpos(cs)), ss) }
| ATOMIC f = lident fs = fun_arg* cs = outline_clause* EQUAL ss = steps
    { `Contract (f, fs, (match cs with [] -> None | _ -> Some $endpos(cs)), ss) }
;

(* A clause of an outline's contract, parenthesized as a lemma's. *)
outline_clause:
| CONTINUES lident {}
| REQUIRES LEFTPAR term RIGHTPAR {}
| ENSURES LEFTPAR term RIGHTPAR {}
| ATOMIC_REQUIRES LEFTPAR term RIGHTPAR {}
| ATOMIC_ENSURES LEFTPAR term RIGHTPAR {}
| RAISES mpat_app ARROW LEFTPAR term RIGHTPAR {}
| RAISES mpat_app {}
| ATOMIC_RAISES mpat_app ARROW LEFTPAR term RIGHTPAR {}
;

(* Steps in program order. [let p = at (a) (fun step -> e) in ...] exports the value that
   the scope returns with the result to the later steps; [let x = e in ...] binds pure
   ghost code for them. *)
outline_steps:
| LEFTPAR RIGHTPAR { [] }
| s = outline_step { [s] }
| s = outline_step SEMICOLON ss = outline_steps { s :: ss }
| LET p = pat EQUAL AT LEFTPAR anchor_loc = anchor RIGHTPAR action = step_action
    IN ss = outline_steps
    { let action, action_loc = action in
      At { anchor_loc; action; action_loc; export = Some p }
      :: ss }
| LET p = pat EQUAL e = proof_expr IN ss = outline_steps
    { Let { pattern = p; value = e } :: ss }
;

nested_steps:
| BEGIN ss = outline_steps END { ss }
;

outline_step:
| INITIALLY initial_expression
    { Initially { initialization_loc = mk_loc $loc } }
| AT LEFTPAR anchor_loc = anchor RIGHTPAR action = step_action
    { let action, action_loc = action in
      At { anchor_loc; action; action_loc; export = None } }
| a = lident LEFTPAR anchor RIGHTPAR step_action
    { raise (Syntax_error (a.pid_loc,
        "A step is at (code) followed by its step, or on return followed by ghost code")) }
| ON r = lident adapter = return_adapter_expr
    { if r.pid_str <> "return" then
        raise (Syntax_error (r.pid_loc, "Expected on return"));
      ignore adapter;
      On_return { return_loc = mk_loc $loc(adapter); return_adapter = true } }
| ON r = lident e = proof_nonseq
    { if r.pid_str <> "return" then
        raise (Syntax_error (r.pid_loc,
          "A step is at (code) followed by its step, or on return followed by ghost code"));
      ignore e;
      On_return { return_loc = mk_loc $loc(e); return_adapter = false } }
| o = outline(nested_steps) { Nested o }
;

(* The code a step follows, or the code bound to a name, as [let head = Atomic.make x]. *)
anchor:
| anchor_token+ { mk_loc $loc }
;

(* Anchors are parsed as OCaml by Outline; this grammar preserves their balanced range. *)
anchor_token:
| LEFTPAR anchor_token* RIGHTPAR { () }
| LEFTSQ anchor_token* RIGHTSQ { () }
| LEFTBRC anchor_token* RIGHTBRC { () }
| LIDENT | UIDENT | OP1 | OP2 | OP3 | OP4
| OPPREF | QUOTE_LIDENT | BACKQUOTE_LIDENT | POLY_TAG | ATTRIBUTE | INTEGER | FLOAT | CHAR
| STRING | REQUIRES | ENSURES | VARIANT | PURE | INVARIANT | PREDICATE
| FOLD | UNFOLD | ASSERT | ATOMIC | ATOMIC_REQUIRES | ATOMIC_ENSURES | ATOMIC_RAISES
| RAISES | COMMIT | RETURNING | TYPE | VIEW | ACTION | INITIALLY
| PERFORMS | CONSUMES | LINEARIZES | LEADSTO | CONTINUES | WAIT | ON
| HELPS | AS | PROOF | AT | LEMMA | RETURNS | OF
| BEGIN | END | MODULE | STRUCT | FUN | SET_OF_PREDICATE | FRACTION | WRITER | RELEASE
| ELSE | EXISTS | FALSE | FORALL | IF | IN | LET
| REC | NONREC | MATCH | NOT | OLD | THEN | TRUE | WITH
| CONJ | AMPAMP | ARROW | BAR | BARBAR | COLON | COLONCOLON
| COMMA | DOT | DOTDOT | EQUAL | LRARROW | LTGT | DISJ
| SEMICOLON | STAR | UNDERSCORE
| LEFTSQRIGHTSQ
    { () }
;

step_action:
| scope_expression { (Wrapped_scope, mk_loc $loc) }
| INVARIANT term { (Loop, mk_loc $loc) }
| INVARIANT LEFTPAR FUN pat_arg ARROW term RIGHTPAR
    { (Loop, mk_loc $loc) }
| COMMIT { (Linearize, mk_loc $loc) }
| COMMIT term_arg { (Linearize, mk_loc $loc) }
| RETURNING mpat ARROW outcome { (Linearize, mk_loc $loc) }
| PERFORMS lident { (Linearize, mk_loc $loc) }
| LEFTPAR FUN lident state = pat_arg? ARROW proof_expr RIGHTPAR
    { if state <> None then
        raise (Syntax_error (mk_loc $loc(state),
          "A step exports a value for later steps as let p = at (code) (fun step -> e)"));
      (Scope, mk_loc $loc) }
| i = lident term_arg
    { if i.pid_str <> "initializes" then
        raise (Syntax_error (i.pid_loc, "Expected commit, returning, performs, \
          initializes or a scope (fun step -> ...)"));
      (Initializes, mk_loc $loc) }
;
;

proof_module_argument:
| LEFTPAR STRUCT TYPE ps = loption(type_parameters) t = lident EQUAL ty = typ END RIGHTPAR
    { if t.pid_str <> "t" then
        raise (Syntax_error (t.pid_loc, "A type argument must define type t"));
      Proof_type_argument { type_params = ps; type_body = ty } }
| LEFTPAR a = uqualid RIGHTPAR
    { Proof_module_argument a }
;

proof_decl:
| p = predicate_decl { Proof_predicate p }
| MODULE n = uident EQUAL ds = proof_module_body
    { let ds, os = ds in
      Proof_module { module_name = n; module_parameters = [];
        module_declarations = ds; module_outlines = os; module_loc = mk_loc $loc } }
| MODULE n = uident ps = proof_module_parameter+ EQUAL ds = proof_module_body
    { let ds, os = ds in
      Proof_module { module_name = n; module_parameters = ps;
        module_declarations = ds; module_outlines = os; module_loc = mk_loc $loc } }
| MODULE n = uident COLON interface = uqualid constraints = proof_definition_constraints
    EQUAL ds = proof_module_body
    { let ds, os = ds in
      Proof_definition { module_name = n; module_interface = interface;
        module_constraints = constraints;
        module_declarations = ds; module_outlines = os; module_loc = mk_loc $loc } }
| MODULE n = uident EQUAL f = uqualid LEFTPAR STRUCT
    LET operation = lident EQUAL target = lqualid END RIGHTPAR
    { let kind = match f with
      | Qdot (Qid ghost, facade)
        when ghost.pid_str = "Ghost" &&
          (facade.pid_str = "AU" || facade.pid_str = "Task") -> facade.pid_str
      | _ -> raise (Syntax_error (qualid_loc f, "Expected Ghost.AU or Ghost.Task"))
      in
      if operation.pid_str <> "operation" then
        raise (Syntax_error (operation.pid_loc,
          "A Ghost." ^ kind ^ " argument must define operation"));
      if kind = "AU" then Proof_au { au_name = n; au_operation = target }
      else Proof_task { task_name = n; task_operation = target } }
| MODULE n = uident EQUAL f = uqualid LEFTPAR STRUCT
    LET field = lident owner = shared_field_owner EQUAL selector = term END RIGHTPAR
    { let kind = match f with
      | Qdot (Qid ghost, facade) when ghost.pid_str = "Ghost" ->
          begin match facade.pid_str with
          | "Frozen" -> Frozen
          | "Relaxed" -> Relaxed
          | "History" -> raise (Syntax_error (qualid_loc f,
              "Ghost.History has been renamed to Ghost.Relaxed"))
          | _ -> raise (Syntax_error (qualid_loc f,
              "Expected Ghost.Frozen or Ghost.Relaxed"))
          end
      | _ -> raise (Syntax_error (qualid_loc f,
          "Expected Ghost.Frozen or Ghost.Relaxed"))
      in
      if field.pid_str <> "field" then
        raise (Syntax_error (field.pid_loc,
          "A shared-field facade argument must define field"));
      Proof_access_field { access_name = n; access_kind = kind;
        access_owner = owner; access_selector = selector } }
| MODULE n = uident EQUAL f = uqualid args = proof_module_argument*
    { Proof_resource { resource_name = n; resource_functor = f; resource_arguments = args } }
| LET recursive = boption(REC) n = lident ps = pred_param* COLON ty = typ
    variants = list(preceded(VARIANT, proof_variant)) EQUAL body = term
    { let field_type = match ty with
        | PTtyapp (Qdot (Qid m, field), [_; _])
          when m.pid_str = "Ghost" && field.pid_str = "field" -> true
        | _ -> false
      in
      let field_init = match body.term_desc with
        | Tapply ({term_desc = Tvar (Qdot (Qid m, f)); _}, {term_desc = Ttuple []; _})
          when m.pid_str = "Ghost" && f.pid_str = "field" -> true
        | _ -> false
      in
      if ps = [] && (field_type || field_init) then begin
        if recursive || variants <> [] then
          raise (Syntax_error (n.pid_loc, "A ghost field cannot be recursive"));
        if not (field_type && field_init) then
          raise (Syntax_error (n.pid_loc,
            "A ghost field declaration requires (owner, value) Ghost.field = Ghost.field ()"));
        Proof_field { field_name = n; field_type = ty }
      end else
        Proof_function { function_name = n; function_params = ps;
          function_result = ty; function_recursive = recursive;
          function_variant = List.concat variants; function_body = body } }
| LEMMA attribute = ATTRIBUTE? n = lident ps = lemma_param* rs = lemma_returns?
    cs = lemma_clause* EQUAL body = proof_expr
    { let requires, ensures, variant, opens =
        List.fold_left
          (fun (requires, ensures, variant, opens) -> function
            | `Requires t -> (t :: requires, ensures, variant, opens)
            | `Ensures t -> (requires, t :: ensures, variant, opens)
            | `Variant t -> (requires, ensures, t :: variant, opens)
            | `Opens (at, entries) ->
                if opens <> None then
                  raise (Syntax_error (at, "A lemma has at most one opens clause"));
                (requires, ensures, variant, Some (at, entries)))
          ([], [], [], None) cs
      in
      let n = match attribute with
        | None -> n
        | Some "auto" -> add_attr n "auto"
        | Some _ -> raise (Syntax_error (mk_loc $loc(attribute), "A lemma's attribute is [@auto]"))
      in
      Proof_lemma {
        lemma_name = n; lemma_params = ps;
        lemma_returns = (match rs with None -> [] | Some rs -> rs);
        lemma_requires = List.rev requires; lemma_ensures = List.rev ensures;
        lemma_variant = List.concat (List.rev variant); lemma_opens = opens; lemma_body = body;
      } }
| TYPE ps = loption(type_parameters) n = lident EQUAL LEFTBRC fs = semicolon_list1(state_field) RIGHTBRC
    { Proof_state { state_name = n; state_params = ps; state_fields = fs } }
| TYPE ps = loption(type_parameters) n = lident EQUAL cs = bar_list1(type_ctor)
    { Proof_type { type_name = n; type_params = ps; type_kind = Variant cs; type_recursive = true } }
| TYPE ps = loption(type_parameters) n = lident EQUAL ty = typ
    { Proof_type { type_name = n; type_params = ps; type_kind = Alias ty; type_recursive = true } }
| TYPE NONREC ps = loption(type_parameters) n = lident EQUAL ty = typ
    { Proof_type { type_name = n; type_params = ps; type_kind = Alias ty; type_recursive = false } }
| INVARIANT n = lident ps = pred_param+ EQUAL t = term
    { let ps = List.rev ps in
      Proof_invariant { inv_name = n; inv_params = List.rev (List.tl ps);
                        inv_state = List.hd ps; inv_body = t } }
| VIEW n = lident ps = pred_param+ EQUAL t = term
    { Proof_view { view_name = n; view_params = ps; view_value = t } }
| ACTION n = lident ps = lident* EQUAL step = action_step?
    LEFTBRC s = lident WITH fs = semicolon_list1(field_value) RIGHTBRC
    ls = loption(preceded(LINEARIZES, separated_nonempty_list(COMMA, lident)))
    h = list(preceded(HELPS, helps))
    { let step, consumes =
        match step with Some (st, c) -> (Some st, c) | None -> (None, None) in
      Proof_action { action_name = n; action_params = ps; action_step = step;
                     action_consumes = consumes; action_state = s; action_update = fs;
                     action_linearizes = ls; action_helps = h } }
;

proof_module_body:
| STRUCT items = proof_item* END { split_items items }
;

shared_field_owner:
| LEFTPAR owner = mpat COLON ty = typ RIGHTPAR { (owner, ty) }
;

proof_definition_constraints:
| { [] }
| WITH TYPE ps = loption(type_parameters) n = lident EQUAL ty = typ
    { if n.pid_str <> "t" then
        raise (Syntax_error (n.pid_loc,
          "A proof-defined module supports a constraint on type t only"));
      [ps, n, ty] }
;

proof_module_parameter:
| LEFTPAR n = uident COLON ty = uqualid RIGHTPAR
    { Proof_named_parameter (n, ty) }
| LEFTPAR RIGHTPAR { Proof_unit_parameter (mk_loc $loc) }
;

type_parameters:
| p = quote_lident { [p] }
| LEFTPAR ps = separated_nonempty_list(COMMA, quote_lident) RIGHTPAR { ps }
;

type_ctor:
| c = uident args = preceded(OF, separated_nonempty_list(STAR, ty_arg))?
    { (c, match args with None -> [] | Some args -> args) }
;

lemma_returns:
| RETURNS rs = pred_param+ { rs }
;

lemma_clause:
| REQUIRES LEFTPAR t = term RIGHTPAR { `Requires t }
| ENSURES LEFTPAR t = term RIGHTPAR { `Ensures t }
| VARIANT t = proof_variant { `Variant t }
| OPENS LEFTBRC ts = loption(semicolon_list1(mask_entry)) RIGHTBRC
    { `Opens (mk_loc $loc, ts) }
;

mask_entry:
| q = qualid args = mask_argument*
    { let wildcard t = match t.term_desc with
        | Tvar (Qid id) -> id.pid_str = "_"
        | _ -> false in
      let _ = List.fold_left (fun seen t ->
        if seen && not (wildcard t) then
          raise (Syntax_error (t.term_loc,
            "Wildcards in an opens entry must be trailing"));
        seen || wildcard t) false args in
      List.fold_left
        (fun f arg -> mk_term (Tapply (f, arg)) (f.term_loc.loc_start, arg.term_loc.loc_end))
        (mk_term (Tvar q) $loc(q)) args }
;

mask_argument:
| t = term_arg { t }
| UNDERSCORE { mk_term (Tvar (Qid (mk_pid "_" $loc))) $loc }
;

proof_variant:
| t = term_arg
    { match t.term_desc with Ttuple ts -> ts | _ -> [t] }
| ts = comma_list2(term_arg) { ts }
;

helps:
| f = term ON k = term p = preceded(AS, mpat)? WITH v = term
    { (f, k, { contents = p; result = v }) }
;

action_step:
| op = lident args = step_arg* c = preceded(CONSUMES, term)? LEADSTO { ((op, args), c) }
;

step_arg:
| UNDERSCORE { None }
| t = term_arg { Some t }
;

state_field:
| x = lident COLON t = typ a = ATTRIBUTE?
    { let helps =
        match a with
        | Some a when String.length a > 6 && String.sub a 0 6 = "helps " ->
            Some (String.sub a 6 (String.length a - 6))
        | _ -> None
      in
      { sf_name = x; sf_type = t; sf_grows = (a = Some "grows"); sf_helps = helps } }
;

annotated_param:
| LEFTPAR x = lident a = ATTRIBUTE? COLON t = typ RIGHTPAR
    { (x, a, mk_loc $loc(a), t) }
;

lemma_param:
| p = annotated_param { implicit_parameter "lemma" p }
;

predicate_param:
| p = annotated_param { implicit_parameter "predicate" p }
;

pred_param:
| LEFTPAR x = lident COLON t = typ RIGHTPAR { (x, t) }
;

outcome:
| COMMIT { Commits }
| COMMIT t = term_arg { Commits_with t }
| WAIT IN f = term ON k = term { Waits (f, k) }
| IF c = term THEN a = outcome ELSE b = outcome { Chooses (c, a, b) }
;

linearization:
| COMMIT EOF { Commit }
| RETURNING p = mpat ARROW o = outcome EOF { Returning (p, o) }
| PERFORMS a = lident EOF { Performs a }
;

initially:
| INITIALLY init = initial_expression EOF { init }
;

initial_expression:
| LEFTBRC fs = semicolon_list1(field_value) RIGHTBRC { Initial_record fs }
| LET p = pat EQUAL value = proof_expr IN body = initial_expression
    { Initial_let (p, value, body) }
;

field_value:
| x = lident EQUAL t = term { (x, t) }
;

ghost_stmts:
| ss = ghost_stmt+ EOF { ss }
;

ghost_stmt:
| FOLD t = term ws = ghost_witnesses?
    { match ws with None -> Fold t | Some ws -> Fold_with (t, ws) }
| UNFOLD t = term ws = ghost_witnesses?
    { match ws with None -> Unfold t | Some ws -> Unfold_with (t, ws) }
| ASSERT t = term { Assert t }
| LEMMA t = term { Ghost_call t }
;

proof_expr:
| e = proof_nonseq %prec below_SEMICOLON { e }
| a = proof_nonseq SEMICOLON b = proof_expr { mk_proof (Proof_seq (a, b)) $loc }
;

proof_nonseq:
| LET p = pat EQUAL value = proof_expr IN body = proof_expr
    { mk_proof (Proof_let (p, value, body)) $loc }
| IF c = proof_value_expr THEN yes = proof_nonseq ELSE no = proof_nonseq
    { mk_proof (Proof_if (term_of_proof c, yes, no)) $loc }
| MATCH t = proof_value_expr WITH ioption(BAR) cases = proof_cases
    { mk_proof (Proof_match (term_of_proof t, cases)) $loc }
| ASSERT t = proof_value_expr
    { mk_proof (Proof_assert (term_of_proof t)) $loc }
| FOLD t = proof_value_expr
    { let t, ws = record_argument (term_of_proof t) in
      mk_proof (Proof_fold (t, ws)) $loc }
| UNFOLD t = proof_value_expr
    { let t, ws = record_argument (term_of_proof t) in
      mk_proof (Proof_unfold (t, List.map (pun_name ~at:(mk_loc $loc)) ws)) $loc }
| BEGIN e = proof_expr END { { e with proof_loc = mk_loc $loc } }
| e = proof_value_expr { e }
;

proof_value_expr:
| e = proof_app { e }
| OLD e = proof_value_expr { proof_term (Told (term_of_proof e)) $loc }
| op = prefix_op e = proof_value_expr %prec prec_prefix_op
    { proof_term (mk_op_apply op [term_of_proof e]) $loc }
| l = proof_value_expr o = infix_op_1 r = proof_value_expr
    { proof_term (Tinfix (term_of_proof l, o, term_of_proof r)) $loc }
| l = proof_value_expr o = infix_op_234 r = proof_value_expr
    { proof_term (mk_op_apply o [term_of_proof l; term_of_proof r]) $loc }
| l = proof_value_expr COLONCOLON r = proof_value_expr
    { proof_term (mk_op_apply (mk_pid ~fixity:Mixfix "::" $loc)
        [term_of_proof l; term_of_proof r]) $loc }
| l = proof_value_expr o = BACKQUOTE_LIDENT r = proof_value_expr
    { proof_term (mk_op_apply (mk_pid o $loc) [term_of_proof l; term_of_proof r]) $loc }
| q = quant l = comma_list1(quant_vars) DOT t = proof_value_expr
    { proof_term (Tquant (q, List.concat l, term_of_proof t)) $loc }
| a = attr t = proof_value_expr %prec prec_named
    { proof_term (Tattr (a, term_of_proof t)) $loc }
;

proof_app:
| e = proof_postfix { e }
| f = proof_app arg = proof_postfix
    { proof_term (Tapply (term_of_proof f, term_of_proof arg)) $loc }
| f = proof_postfix labels = nonempty_list(own_label(proof_own_arg))
    location = proof_postfix value = proof_postfix
    { proof_term (own_application (term_of_proof f) labels
        (term_of_proof location) (term_of_proof value) $loc) $loc }

;

proof_own_arg:
| e = proof_postfix { term_of_proof e }
;

%inline own_label(X):
| FRACTION COLON value = X { `Fraction value }
| WRITER COLON value = X { `Writer value }
| RELEASE COLON value = X { `Release value }
;

proof_postfix:
| e = proof_value_atom { e }
| f = proof_postfix DOT q = lqualid_rich
    { proof_term (Tfield (term_of_proof f, q)) $loc }
| f = proof_postfix DOT LEFTPAR i = proof_expr RIGHTPAR
    { proof_term (mk_op_apply (mk_pid ~fixity:Mixfix "([])" $loc)
        [term_of_proof f; term_of_proof i]) $loc }
;

proof_value_atom:
| c = comprehension { proof_value c }
| NOT { proof_term (Tvar (Qid (mk_pid "not" $loc))) $loc }
| q = lqualid { proof_term (Tvar q) $loc }
| q = uqualid %prec below_BAR { proof_term (Tvar q) $loc }
| c = constant { proof_term (Tconst c) $loc }
| TRUE { proof_term Ttrue $loc }
| FALSE { proof_term Tfalse $loc }
| LEFTPAR RIGHTPAR { proof_term (Ttuple []) $loc }
| LEFTPAR e = proof_expr RIGHTPAR { { e with proof_loc = mk_loc $loc } }
| LEFTPAR e = proof_value_expr COLON ty = typ RIGHTPAR
    { proof_term (Tcast (term_of_proof e, ty)) $loc }
| LEFTPAR first = proof_nonseq COMMA rest = comma_list1(proof_nonseq) RIGHTPAR
    { proof_term (Ttuple (List.map term_of_proof (first :: rest))) $loc }
| LEFTSQRIGHTSQ { proof_term (Tvar (Qid (mk_pid "[]" $loc))) $loc }
| LEFTBRC fs = semicolon_list1(proof_field) RIGHTBRC
    { proof_term (Trecord (None, fs)) $loc }
| LEFTBRC r = proof_postfix WITH fs = semicolon_list1(proof_field) RIGHTBRC
    { proof_term (Trecord (Some (term_of_proof r), fs)) $loc }
| LEFTSQ ts = semicolon_list1(proof_nonseq) RIGHTSQ
    { let nil = mk_term (Tvar (Qid (mk_pid "[]" $loc($3)))) $loc($3) in
      let cons e l =
        let t = term_of_proof e in
        mk_term (mk_op_apply (mk_id ~fixity:Mixfix ~loc:t.term_loc "::") [ t; l ]) $loc
      in
      proof_value (List.fold_right cons ts nil) }
;

(* A field of a record, [f = e], or [f] for [f = f]. *)
proof_field:
| x = lident EQUAL e = proof_nonseq { (x, term_of_proof e) }
| x = lident { (x, mk_term (Tvar (Qid x)) $loc) }
;

proof_cases:
| c = proof_case %prec below_BAR { [c] }
| c = proof_case BAR cs = proof_cases { c :: cs }
;

proof_case:
| p = mpat ARROW e = proof_expr { (p, e) }
;

ghost_witnesses:
| WITH LEFTBRC ws = semicolon_list1(field_value) RIGHTBRC { ws }
;

loop_clause:
| INVARIANT t = term { `Invariant t }
| INVARIANT LEFTPAR FUN state = pat_arg ARROW t = term RIGHTPAR
    { `State_invariant (state, t) }
| VARIANT t = term { `Variant t }
| RAISES p = mpat_app ARROW t = term { `Raises (p, Some t) }
| RAISES p = mpat_app { `Raises (p, None) }
;

clause:
| REQUIRES t = term { `Requires, t }
| ENSURES t = term { `Ensures, t }
| ATOMIC_REQUIRES t = term { `Atomic_requires, t }
| ATOMIC_ENSURES t = term { `Atomic_ensures, t }
| RAISES p = mpat_app ARROW t = term { `Raises (p, Some t), t }
| RAISES p = mpat_app { `Raises (p, None), mk_term Ttrue $loc }
| ATOMIC_RAISES p = mpat_app ARROW t = term { `Atomic_raises (p, t), t }
| VARIANT t = term { `Variant, t }
| PURE { `Pure, mk_term Ttrue $loc }
| CONTINUES f = lident { `Continues f, mk_term Ttrue $loc }
;

header_app:
| nm=lident_rich args=fun_arg*
    { nm, args }
|  arg1=fun_arg nm=op_symbol arg2=fun_arg
    { let nm = mk_id ~loc:(mk_loc $loc(nm)) nm in
        nm, [arg1; arg2] }

header:
| ret=ret_name EQUAL atomic=boption(ATOMIC) app = header_app
  { let nm, args = app in
    atomic, { hd_name = nm; hd_ret = ret; hd_args = args } }
| app = header_app
  { let nm, args = app in
    false, { hd_name = nm; hd_ret = [ Lwild ]; hd_args = args } }
| ATOMIC app = header_app
  { let nm, args = app in
    true, { hd_name = nm; hd_ret = [ Lwild ]; hd_args = args } }
;

fun_arg:
| LEFTPAR RIGHTPAR
  { Lunit (mk_loc $loc) }
| id = lident
  { Lvar id }
| LEFTSQ id=lident COLON ty=typ RIGHTSQ
  { Lghost (id, ty) }
;

ret_value:
| id = lident
  { Lvar id }
| LEFTSQ id=lident COLON ty=typ RIGHTSQ
  { Lghost (id, ty) }
;


ret_pat_:
| (* *)
  { [] }
| LEFTPAR RIGHTPAR
  { [ Lunit (mk_loc $loc) ] }
| LEFTPAR l=comma_list(ret_value) RIGHTPAR
  { l }
| UNDERSCORE { [ Lwild ] };

ret_name:
| l = separated_nonempty_list(COMMA, ret_value) { l }
| l = ret_pat_ { l }

cast:
| COLON ty = ty_arg  { ty }
;

term: t = mk_term(term_) { t }
;

term_:
| term_arg_
    { chain_desc $1 }
| NOT t = term
    { mk_op_apply (mk_pid "not" $loc($1)) [t] }
| OLD term
    { Told $2 }
| op = prefix_op t = term %prec prec_prefix_op
    { mk_op_apply op [t] }
| l = term ; o = infix_op_1 ; r = term
    { Tinfix (l, o, r) }
| l = term ; o = infix_op_234 ; r = term
    { mk_op_apply o [l; r] }
| l = term ; COLONCOLON ; r = term
    { mk_op_apply (mk_pid ~fixity:Mixfix "::" $loc) [l; r] }
| l = term ; o = BACKQUOTE_LIDENT ; r = term
    { mk_op_apply (mk_pid o $loc) [l; r] }
| term_arg located(term_arg)+
    { let join f (a, e) = mk_term (Tapply (f, a)) ($startpos, e) in
      (List.fold_left join $1 $2).term_desc }
| f = term_arg labels = nonempty_list(own_label(term_arg))
    location = term_arg value = term_arg
    { own_application f labels location value $loc }
| IF g = term THEN t1 = term ELSE t2 = term
    { Tif (g, t1, t2) }
| LET ids = pat EQUAL t1 = term IN t2 = term
   { Tlet(ids, t1, t2) }
| LET id = attrs(lident_op_id) EQUAL t1 = term IN t2 = term
   { Tlet (mk_pat (Pid id) $loc(id), t1, t2) }
| q = quant l = comma_list1(quant_vars) DOT t = term
    { Tquant (q, List.concat l, t) }
| MATCH t = term WITH ioption(BAR) cases = match_cases
    { Tmatch (t, cases) }
| a = attr t = term %prec prec_named
    { Tattr (a, t) }
| t = term ty = cast
    { Tcast (t, ty) }
;


(* As in OCaml, the cases of a match extend as far as possible. *)
match_cases:
| c = match_case %prec below_BAR { [c] }
| c = match_case BAR cs = match_cases { c :: cs }
;

match_case:
| p = mpat ARROW t = term { p, t }
;

(* The patterns of match cases, as OCaml's: tuples of [::]s of constructor applications. *)
mpat:
| p = mpat_cons { p }
| l = comma_list2(mpat_cons) { mk_pat (Ptuple l) $loc }
;

mpat_cons:
| p = mpat_app { p }
| a = mpat_app COLONCOLON b = mpat_cons
    { let args = mk_pat (Ptuple [a; b]) $loc in
      mk_pat (Pconstr (Qid (mk_pid ~fixity:Infix "::" $loc($2)), Some args)) $loc }
;

mpat_app:
| p = mpat_arg { p }
| c = uqualid a = mpat_arg { mk_pat (Pconstr (c, Some a)) $loc }
;

mpat_arg: p = mpat_arg_ { mk_pat p $loc }
;

mpat_arg_:
| UNDERSCORE { Pwild }
| v = lident { Pid v }
| c = constant { Pconst c }
| c = uqualid { Pconstr (c, None) }
| TRUE { Pconstr (Qid (mk_pid "true" $loc), None) }
| FALSE { Pconstr (Qid (mk_pid "false" $loc), None) }
| LEFTSQRIGHTSQ { Pconstr (Qid (mk_pid "[]" $loc), None) }
| LEFTPAR RIGHTPAR { Pconstr (Qid (mk_pid "()" $loc), None) }
| LEFTPAR p = mpat RIGHTPAR { p.pat_desc }
;

pat_arg:
| p = pat_arg_ { mk_pat p $loc }

pat_arg_:
| UNDERSCORE { Pwild }
| v=lident { Pid v }
| LEFTPAR RIGHTPAR { Ptuple [] }
| LEFTPAR p=pat_ RIGHTPAR { p }

pat:
| p=pat_ { mk_pat p $loc }

pat_:
| p=pat_arg_ { p }
| l=comma_list2(pat_arg) { Ptuple l }
| p=pat_arg COLON t=typ { Pcast (p, t) }

quant_vars:
| l = binder_var+ ty = cast? { List.map (fun id -> id, ty) l }
;

attrs(X): l=X a=attr* { List.fold_left (fun acc s -> add_attr acc s) l a }
;

attr:
| a = ATTRIBUTE    { a }
;

term_arg: t = mk_term(term_arg_) { t };
term_dot: t = mk_term(term_dot_) { t }
;

term_arg_:
| c = comprehension        { c.term_desc }
| q = qualid                { Tvar q }
| c = constant              { Tconst c }
| TRUE                      { Ttrue }
| FALSE                     { Tfalse }
| o = oppref ; a = term_arg { mk_op_apply o [a] }
| t = term_sub_             { t }
;

term_dot_:
| q = lqualid               { Tvar q }
| o = oppref ; a = term_dot { mk_op_apply o [a] }
| t = term_sub_             { t }
;

comprehension:
| SET_OF_PREDICATE LEFTPAR FUN b = pred_param ARROW body = term RIGHTPAR
    { mk_term (Tcomprehension (b, body)) $loc }
;

term_block_:
| LEFTPAR t=term RIGHTPAR                           { t.term_desc }
| LEFTPAR RIGHTPAR                                  { Ttuple [] }
| LEFTSQRIGHTSQ
    { Tvar (Qid (mk_pid "[]"  $loc)) }
| LEFTBRC fs = semicolon_list1(field_value) RIGHTBRC
    { Trecord (None, fs) }
| LEFTBRC r = term_arg WITH fs = semicolon_list1(field_value) RIGHTBRC
    { Trecord (Some r, fs) }
| LEFTSQ ts = semicolon_list1(term) RIGHTSQ
    { let nil = mk_term (Tvar (Qid (mk_pid "[]" $loc($3)))) $loc($3) in
      let cons t l =
        mk_term (mk_op_apply (mk_id ~fixity:Mixfix ~loc:t.term_loc "::") [ t; l ]) $loc
      in
      (List.fold_right cons ts nil).term_desc }
;

term_sub_:
| t = term_block_
    { t }
| t = term_dot DOT q = lqualid_rich
    { Tfield (t, q) }
| t = term_dot DOT LEFTPAR i = term RIGHTPAR
    { mk_op_apply (mk_pid ~fixity:Mixfix "([])" $loc) [t; i] }
| LEFTPAR l = comma_list2(term) RIGHTPAR                { Ttuple l }
;

quant:
| FORALL  { Tforall }
| EXISTS  { Texists }
;

constant:
| v = INTEGER { let i, m = v in Pconst_integer (i, m) }
| v = FLOAT { Pconst_float v }
| s = STRING { Pconst_string (s, mk_loc $loc) }
| c = CHAR { Pconst_char c }
;

binder_var:
| l = attrs(lident)  { l }
;


typ:
| v = ty_arg
    { v }
| arg = typ ARROW ret = typ
    { PTarrow (arg, ret) }
| t = ty_arg STAR l = ty_tuple
    { PTtuple (t :: l) }
;


ty_tuple:
| arg = ty_arg
    { [arg] }
| ty = ty_arg STAR l = ty_tuple
    { ty :: l }
;

ty_arg:
| UNDERSCORE
    { PTtyany }
| q = lqualid
    { PTtyapp (q, []) }
| v = quote_lident
    { PTtyvar v }
| LEFTSQ tags = row_tags RIGHTSQ
    { PTvariant (Closed_row, tags) }
| LEFTSQ bound = OP1 tags = row_tags RIGHTSQ
    { let bound = match bound with
        | ">" -> Lower_row
        | "<" -> Upper_row
        | _ -> raise (Syntax_error (mk_loc $loc(bound),
            "A polymorphic-variant type bound is < or >"))
      in PTvariant (bound, tags) }
| LEFTPAR ty = typ RIGHTPAR
    { ty }
| ty = ty_arg q = lqualid
    { PTtyapp (q, [ty]) }
| LEFTPAR ty = typ COMMA l = separated_nonempty_list(COMMA, typ)  RIGHTPAR id=lqualid
    { PTtyapp (id, ty :: l) }
;

row_tags:
| tags = separated_nonempty_list(BAR, row_tag) { tags }
;

row_tag:
| tag = POLY_TAG { mk_pid tag $loc }
| tag = POLY_TAG OF typ
    { raise (Syntax_error (mk_loc $loc,
        "Polymorphic-variant type indices support constant tags only: `" ^ tag)) }
;


mk_term(X): d = X { mk_term d $loc }
;

(* Symbolic operation names *)

op_symbol:
| o = OP1 { o }
| o = OP2 { o }
| o = OP3 { o }
| o = OP4 { o }
| ARROW   { "->" }
| LRARROW { "<->" }
| BARBAR  { "||" }
| AMPAMP  { "&&" }
| STAR    { "*"  }
;

%inline oppref:
| o = OPPREF { mk_pid ~fixity:Prefix o $loc }
;

prefix_op:
| o = op_symbol { mk_pid ~fixity:Prefix o $loc }
;

%inline infix_op_1:
| o = OP1   { mk_pid ~fixity:Infix o $loc }
| EQUAL     { mk_pid ~fixity:Infix "=" $loc }
| LTGT      { mk_pid ~fixity:Infix "<>" $loc }
%inline infix_op_234:
| o = OP2   { mk_pid ~fixity:Infix o $loc }
| o = OP3   { mk_pid ~fixity:Infix o $loc }
| STAR      { mk_pid ~fixity:Infix "*" $loc }
| o = OP4   { mk_pid ~fixity:Infix o $loc }
| ARROW     { mk_pid ~fixity:Infix "->"  $loc }
| LRARROW   { mk_pid ~fixity:Infix "<->" $loc }
| DISJ      { mk_pid ~fixity:Infix "\\/" $loc }
| BARBAR    { mk_pid ~fixity:Infix "||"  $loc }
| CONJ      { mk_pid ~fixity:Infix "/\\" $loc }
| AMPAMP    { mk_pid ~fixity:Infix "&&"  $loc }
;

(* Idents *)

lident:
| id = LIDENT        { mk_pid id $loc }
;

uident:
| id = UIDENT        { mk_pid id $loc }
;

quote_lident:
| id = QUOTE_LIDENT  { mk_pid id $loc }
;

ident_rich:
| id = uident        { id }
| id = lident_rich   { id }
;

lident_rich:
| id = lident        { id }
| id = lident_op_id  { id }
;

lident_fun_id:
| LEFTPAR id = lident_op RIGHTPAR  { mk_pid id $loc }

lident_op_id:
| id = lident_fun_id               { id }
| LEFTPAR DISJ RIGHTPAR            { mk_pid ~fixity:Infix "\\/" $loc }
| LEFTPAR CONJ RIGHTPAR            { mk_pid  ~fixity:Infix "/\\" $loc }
;

lident_op:
| op = op_symbol                              { op }
| op = op_symbol UNDERSCORE                   { op }
| EQUAL                                       { "=" }
| LTGT                                        { "<>" }
| op = OPPREF UNDERSCORE?                     { op }
| DOT LEFTPAR RIGHTPAR                        { ".()" }
| LEFTSQ UNDERSCORE RIGHTSQ                   { "[_]" }
| LEFTSQ ARROW RIGHTSQ                        { "[->]" }
| LEFTSQ UNDERSCORE DOTDOT UNDERSCORE RIGHTSQ { "[_.._]" }
| LEFTSQ            DOTDOT UNDERSCORE RIGHTSQ { "[.._]" }
| LEFTSQ UNDERSCORE DOTDOT            RIGHTSQ { "[_..]" }
;

(* Qualified idents *)

qualid:
| id = ident_rich                  { Qid id }
| q = uqualid DOT id = ident_rich  { Qdot (q, id) }
| q = uqualid DOT COMMIT { Qdot (q, mk_pid "commit" $loc) }
| q = uqualid DOT AT { Qdot (q, mk_pid "at" $loc) }
;

lqualid_rich:
| id = lident_rich                 { Qid id }
| q = uqualid DOT id = lident_rich { Qdot (q, id) }
| q = uqualid DOT COMMIT { Qdot (q, mk_pid "commit" $loc) }
| q = uqualid DOT AT { Qdot (q, mk_pid "at" $loc) }
;

lqualid:
| id = lident                      { Qid id }
| q = uqualid DOT id = lident      { Qdot (q, id) }
| q = uqualid DOT COMMIT { Qdot (q, mk_pid "commit" $loc) }
| q = uqualid DOT AT { Qdot (q, mk_pid "at" $loc) }
;

uqualid:
| id = uident                      { Qid id }
| q = uqualid DOT id = uident      { Qdot (q, id) }
;

(* Miscellaneous *)

comma_list(X):
| l = separated_nonempty_list(COMMA, X) { l }
;

bar_list1(X):
| ioption(BAR) ; xl = separated_nonempty_list(BAR, X) { xl }
;

with_list1(X):
| l = separated_nonempty_list(WITH, X)  { l }
;

comma_list2(X):
| hd = X COMMA l = comma_list1(X) { hd :: l }
;

comma_list1(X):
| l = separated_nonempty_list(COMMA, X) { l }
;

semicolon_list1(X):
| x = X ; ioption(SEMICOLON)                  { [x] }
| x = X ; SEMICOLON ; xl = semicolon_list1(X) { x :: xl }
;

star_list2(X):
| x = X STAR l = separated_nonempty_list(STAR, X) { x :: l }
;

located(X): x = X { x, $endpos }

located_begin(X) : x = X { x, $startpos }

location(X) : X { $loc($1) }
;
