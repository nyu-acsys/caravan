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


  let add_clause c (keyword, t) =
    match keyword with
    | `Requires -> { c with requires = t :: c.requires }
    | `Ensures -> { c with ensures = t :: c.ensures }
    | `Atomic_requires -> { c with atomic_requires = t :: c.atomic_requires }
    | `Atomic_ensures -> { c with atomic_ensures = t :: c.atomic_ensures }
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
             variant = List.rev c.variant }
%}

(* Tokens *)

%token <string> LIDENT UIDENT
%token <string> OP1 OP2 OP3 OP4 OPPREF
%token <string> QUOTE_LIDENT
%token <string> BACKQUOTE_LIDENT
%token <string> ATTRIBUTE

%token <string * char option> INTEGER
%token <string> FLOAT
%token <char> CHAR
%token <string> STRING

(* Contract tokens *)

%token REQUIRES ENSURES VARIANT PURE INVARIANT PREDICATE FOLD UNFOLD ASSERT ATOMIC
%token ATOMIC_REQUIRES ATOMIC_ENSURES COMMIT RETURNING TYPE VIEW LEFTBRC RIGHTBRC
%token ACTION INITIALLY PERFORMS CONSUMES LINEARIZES LEADSTO CONTINUES

(* Keywords *)

%token ELSE EXISTS FALSE FORALL IF IN LET MATCH NOT OLD THEN TRUE WITH

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
%start <Spec_ast.loop_spec> loop_spec
%start <Spec_ast.predicate> predicate
%start <Spec_ast.proof_decl list> proof
%start <Spec_ast.ghost_stmt list> ghost_stmts
%start <Spec_ast.linearization> linearization
%start <(Spec_ast.id * Spec_ast.term) list> initially
%%

contract:
| h = header? cs = clause* EOF { mk_contract h cs }
;

term_eof:
| t = term EOF { t }
;

loop_spec:
| cs = loop_clause* EOF
    { let invariants = List.filter_map (function `Invariant t -> Some t | `Variant _ -> None) cs in
      let loop_variant = List.filter_map (function `Variant t -> Some t | `Invariant _ -> None) cs in
      { invariants; loop_variant } }
;

predicate:
| p = predicate_decl EOF { p }
;

predicate_decl:
| PREDICATE n = lident ps = pred_param+ a = ATTRIBUTE? t = preceded(EQUAL, term)?
    { { pred_name = n; pred_params = ps; pred_body = t;
        pred_persistent = (a = Some "persistent") } }
;

(* The declarations of a proof file. *)
proof:
| ds = proof_decl* EOF { ds }
;

proof_decl:
| p = predicate_decl { Proof_predicate p }
| TYPE n = lident EQUAL LEFTBRC fs = semicolon_list1(state_field) RIGHTBRC
    { Proof_state { state_name = n; state_fields = fs } }
| INVARIANT n = lident ps = pred_param+ EQUAL t = term
    { let ps = List.rev ps in
      Proof_invariant { inv_name = n; inv_params = List.rev (List.tl ps);
                        inv_state = List.hd ps; inv_body = t } }
| VIEW n = lident ps = pred_param+ EQUAL t = term
    { Proof_view { view_name = n; view_params = ps; view_value = t } }
| ACTION n = lident ps = lident* EQUAL step = action_step?
    LEFTBRC s = lident WITH fs = semicolon_list1(field_value) RIGHTBRC
    ls = loption(preceded(LINEARIZES, separated_nonempty_list(COMMA, lident)))
    { let step, consumes =
        match step with Some (st, c) -> (Some st, c) | None -> (None, None) in
      Proof_action { action_name = n; action_params = ps; action_step = step;
                     action_consumes = consumes; action_state = s; action_update = fs;
                     action_linearizes = ls } }
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
    { { sf_name = x; sf_type = t; sf_grows = (a = Some "grows") } }
;

pred_param:
| LEFTPAR x = lident COLON t = typ RIGHTPAR { (x, t) }
;

linearization:
| COMMIT EOF { Commit }
| RETURNING p = mpat ARROW COMMIT EOF { Returning p }
| PERFORMS a = lident EOF { Performs a }
;

initially:
| INITIALLY LEFTBRC fs = semicolon_list1(field_value) RIGHTBRC EOF { fs }
;

field_value:
| x = lident EQUAL t = term { (x, t) }
;

ghost_stmts:
| ss = ghost_stmt+ EOF { ss }
;

ghost_stmt:
| FOLD t = term { Fold t }
| UNFOLD t = term { Unfold t }
| ASSERT t = term { Assert t }
;

loop_clause:
| INVARIANT t = term { `Invariant t }
| VARIANT t = term { `Variant t }
;

clause:
| REQUIRES t = term { `Requires, t }
| ENSURES t = term { `Ensures, t }
| ATOMIC_REQUIRES t = term { `Atomic_requires, t }
| ATOMIC_ENSURES t = term { `Atomic_ensures, t }
| VARIANT t = term { `Variant, t }
| PURE { `Pure, mk_term Ttrue $loc }
| CONTINUES f = lident { `Continues f, mk_term Ttrue $loc }
;

header_app:
| nm=lident_rich args=fun_arg+
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
| LEFTPAR p=pat_ RIGHTPAR { p }

pat:
| p=pat_ { mk_pat p $loc }

pat_:
| p=pat_arg_ { p }
| l=comma_list2(pat_arg) { Ptuple l }
| p=pat_arg t=cast { Pcast (p, t) }

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

term_block_:
| LEFTPAR t=term RIGHTPAR                           { t.term_desc }
| LEFTPAR RIGHTPAR                                  { Ttuple [] }
| LEFTSQRIGHTSQ
    { Tvar (Qid (mk_pid "[]"  $loc)) }
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
| q = lqualid
    { PTtyapp (q, []) }
| v = quote_lident
    { PTtyvar v }
| LEFTPAR ty = typ RIGHTPAR
    { ty }
| ty = ty_arg q = lqualid
    { PTtyapp (q, [ty]) }
| LEFTPAR ty = typ COMMA l = separated_nonempty_list(COMMA, typ)  RIGHTPAR id=lqualid
    { PTtyapp (id, ty :: l) }
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
;

lqualid_rich:
| id = lident_rich                 { Qid id }
| q = uqualid DOT id = lident_rich { Qdot (q, id) }
;

lqualid:
| id = lident                      { Qid id }
| q = uqualid DOT id = lident      { Qdot (q, id) }
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
