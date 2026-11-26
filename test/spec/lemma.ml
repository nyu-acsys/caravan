open Caravan_spec
open Spec_ast

let parse_proof source =
  let lexbuf = Lexing.from_string source in
  try (Spec_parser.proof Spec_lexer.token lexbuf).declarations
  with Spec_parser.Error ->
    failwith
      (Printf.sprintf "proof syntax error at %d (%S)" (Lexing.lexeme_start lexbuf)
         (Lexing.lexeme lexbuf))

let parse_ghost source =
  let lexbuf = Lexing.from_string source in
  Spec_parser.ghost_stmts Spec_lexer.token lexbuf

let parse_ghost_module source =
  let lexbuf = Lexing.from_string source in
  Spec_parser.ghost_module_declaration Spec_lexer.token lexbuf

let parse_invariant_declaration source =
  let lexbuf = Lexing.from_string source in
  Spec_parser.invariant_declaration Spec_lexer.token lexbuf

let rec proof_kinds expr =
  match expr.proof_desc with
  | Proof_value _ -> [ "value" ]
  | Proof_let (_, value, body) -> ("let" :: proof_kinds value) @ proof_kinds body
  | Proof_seq (a, b) -> ("seq" :: proof_kinds a) @ proof_kinds b
  | Proof_if (_, yes, no) -> ("if" :: proof_kinds yes) @ proof_kinds no
  | Proof_match (_, cases) ->
      "match" :: List.concat_map (fun (_, body) -> proof_kinds body) cases
  | Proof_assert _ -> [ "assert" ]
  | Proof_cut _ -> [ "cut" ]
  | Proof_fold (_, witnesses) ->
      [ (if witnesses = [] then "fold" else "fold with witnesses") ]
  | Proof_unfold (_, names) -> [ (if names = [] then "unfold" else "unfold with names") ]

let () =
  begin match parse_ghost_module "module R : ResourceAlgebra" with
  | {
   ghost_module_name = { pid_str = "R"; _ };
   ghost_module_interface = Qid { pid_str = "ResourceAlgebra"; _ };
  } ->
      ()
  | _ -> failwith "abstract proof module was not parsed"
  end;
  begin match parse_ghost_module "module R : Library.ResourceAlgebra" with
  | { ghost_module_interface = Qdot (Qid _, { pid_str = "ResourceAlgebra"; _ }); _ } -> ()
  | _ -> failwith "qualified abstract proof module interface was not parsed"
  end;
  let proof =
    parse_proof
      {|lemma step (x : int) (y : int) returns (r : int) (s : int)
        requires (x >= 0) ensures (r = x) variant (y) = begin
          let (z : int) = x in
          let (r, s) = split z in
          assert r >= 0;
          fold p r { witness = z; };
          let (value : int) = unfold p r { witness } in
          if r = 0 then () else
            match s with | 0 -> () | _ -> (r, s)
        end
        lemma empty = ()
        lemma simple_fold = fold p x
        lemma simple_unfold = unfold p x
        lemma grouped = (assert true)|}
  in
  begin match proof with
  | [
   Proof_lemma l;
   Proof_lemma empty;
   Proof_lemma fold;
   Proof_lemma unfold;
   Proof_lemma grouped;
  ] ->
      assert (l.lemma_name.pid_str = "step");
      assert (List.length l.lemma_params = 2);
      assert (List.length l.lemma_returns = 2);
      assert (List.length l.lemma_requires = 1);
      assert (List.length l.lemma_ensures = 1);
      assert (List.length l.lemma_variant = 1);
      begin match l.lemma_body.proof_desc with
      | Proof_let ({ pat_desc = Pcast _; _ }, _, _) -> ()
      | _ -> failwith "typed let pattern was not parsed"
      end;
      let kinds = proof_kinds l.lemma_body in
      List.iter
        (fun kind -> assert (List.mem kind kinds))
        [
          "let";
          "seq";
          "assert";
          "fold with witnesses";
          "unfold with names";
          "if";
          "match";
          "value";
        ];
      assert (proof_kinds empty.lemma_body = [ "value" ]);
      assert (proof_kinds fold.lemma_body = [ "fold" ]);
      assert (proof_kinds unfold.lemma_body = [ "unfold" ]);
      assert (proof_kinds grouped.lemma_body = [ "assert" ])
  | _ -> failwith "unexpected proof declarations"
  end;
  begin match parse_ghost "fold p x unfold p x assert true" with
  | [ Fold _; Unfold _; Assert _ ] -> ()
  | _ -> failwith "legacy ghost annotations changed"
  end;
  begin match parse_ghost "lemma helper x" with
  | [ Ghost_call _ ] -> ()
  | _ -> failwith "ghost lemma annotation was not parsed"
  end;
  begin match
    parse_proof
      {|lemma precedence = f x.y + z
        lemma sequence = if true then assert true else (); assert false
        lemma cast = let (pair : int * int) = (x : int * int) in pair
        lemma negation = not x = y
        lemma match_sequence = match x with A -> (); assert true | B -> ()|}
  with
  | [
   Proof_lemma precedence;
   Proof_lemma sequence;
   Proof_lemma cast;
   Proof_lemma negation;
   Proof_lemma match_sequence;
  ] ->
      begin match precedence.lemma_body.proof_desc with
      | Proof_value { term_desc = Tapply ({ term_desc = Tapply (_, left); _ }, _); _ } ->
          begin match left.term_desc with
          | Tapply (_, { term_desc = Tfield _; _ }) -> ()
          | _ -> failwith "field access did not bind within the call argument"
          end
      | _ -> failwith "field, application, or infix precedence changed"
      end;
      begin match sequence.lemma_body.proof_desc with
      | Proof_seq ({ proof_desc = Proof_if _; _ }, { proof_desc = Proof_assert _; _ }) ->
          ()
      | _ -> failwith "semicolon escaped the if branches incorrectly"
      end;
      begin match cast.lemma_body.proof_desc with
      | Proof_let
          ( { pat_desc = Pcast (_, PTtuple [ _; _ ]); _ },
            { proof_desc = Proof_value { term_desc = Tcast (_, PTtuple [ _; _ ]); _ }; _ },
            _ ) ->
          ()
      | _ -> failwith "tuple type annotations were not parsed"
      end;
      begin match negation.lemma_body.proof_desc with
      | Proof_value { term_desc = Tinfix ({ term_desc = Tapply _; _ }, _, _); _ } -> ()
      | _ -> failwith "not must bind as an OCaml function application"
      end;
      begin match match_sequence.lemma_body.proof_desc with
      | Proof_match (_, [ (_, { proof_desc = Proof_seq _; _ }); _ ]) -> ()
      | _ -> failwith "semicolon did not remain inside the match case"
      end
  | _ -> failwith "unexpected proof precedence declarations"
  end;
  begin match
    parse_proof
      {|type link = | Linked of node Atomic.t * int * node Atomic.t | Empty
        type state = (* a state comment *) { count : int }
        type piece = { before : int list; after : int list }
        invariant counted (t : t) (s : state) = true
        action dec = (* an action comment *) { s with count = s.count - 1 }|}
  with
  | [
   Proof_type { type_name; type_kind = Variant [ (linked, args); (empty, []) ]; _ };
   Proof_state _;
   Proof_type { type_name = piece; type_kind = Record [ _; _ ]; _ };
   Proof_invariant _;
   Proof_action _;
  ] ->
      assert (type_name.pid_str = "link");
      assert (linked.pid_str = "Linked");
      assert (List.length args = 3);
      assert (empty.pid_str = "Empty");
      assert (piece.pid_str = "piece")
  | _ -> failwith "unexpected logical type or state declarations"
  end;
  begin match
    parse_proof
      {|type 'a edge = Edge of 'a
        type ('a, 'b) pair = { first : 'a; second : 'b }|}
  with
  | [
   Proof_type { type_params = [ a ]; type_kind = Variant [ (_, [ PTtyvar payload ]) ]; _ };
   Proof_type { type_params = [ first; second ]; type_kind = Record [ _; _ ]; _ };
  ] ->
      assert (a.pid_str = "a");
      assert (payload.pid_str = "a");
      assert (first.pid_str = "a");
      assert (second.pid_str = "b")
  | _ -> failwith "unexpected parameterized logical type declarations"
  end;
  begin match
    parse_proof
      {|type 'a state = { current : 'a; values : 'a sequence [@grows] }
        type ('a, 'b) pair = { first : 'a; second : 'b }
        invariant shared (cell : 'a t) (s : 'a state) = true|}
  with
  | [
   Proof_state
     { state_params = [ parameter ]; state_fields = [ _; { sf_grows = true; _ } ]; _ };
   Proof_type { type_params = [ _; _ ]; type_kind = Record [ _; _ ]; _ };
   Proof_invariant { inv_state = _, PTtyapp (_, [ PTtyvar argument ]); _ };
  ] ->
      assert (parameter.pid_str = "a");
      assert (argument.pid_str = "a")
  | _ -> failwith "unexpected parameterized state declarations"
  end;
  begin match parse_proof "module Authority = Auth (Owner.Facts)" with
  | [
   Proof_resource
     { resource_arguments = [ Proof_module_argument (Qdot (Qid owner, facts)) ]; _ };
  ] ->
      assert (owner.pid_str = "Owner");
      assert (facts.pid_str = "Facts")
  | _ -> failwith "qualified resource argument was not parsed"
  end;
  begin match
    parse_proof
      {|module Facts = SetRA (struct type 'a t = 'a fact end)
        module Authority = Auth (Facts)
        module Pair = Product
          (struct type ('a, 'b) t = 'a left end)
          (struct type ('x, 'y) t = 'y right end)|}
  with
  | [
   Proof_resource
     { resource_arguments = [ Proof_type_argument { type_params = [ a ]; _ } ]; _ };
   Proof_resource { resource_arguments = [ Proof_module_argument _ ]; _ };
   Proof_resource
     {
       resource_arguments =
         [
           Proof_type_argument { type_params = [ first; second ]; _ };
           Proof_type_argument { type_params = [ left; right ]; _ };
         ];
       _;
     };
  ] ->
      assert (a.pid_str = "a");
      assert (first.pid_str = "a");
      assert (second.pid_str = "b");
      assert (left.pid_str = "x");
      assert (right.pid_str = "y")
  | _ -> failwith "parameterized resource arguments were not parsed"
  end;
  begin match
    parse_proof
      {|type fact = Seen of int
        module Facts = SetRA (struct type t = fact end)
        module Authority = Auth (Facts)
        let facts : (node Atomic.t, Authority.t) Ghost.field = Ghost.field ()
        let facts_of (x : int) : fact set =
          Set.of_predicate (fun (f : fact) -> f = Seen x)
        lemma use (x : int) =
          let known = Set.of_predicate (fun (f : fact) -> f = Seen x) in
          assert Set.mem (Seen x) known|}
  with
  | [
   Proof_type _;
   Proof_resource
     { resource_name = facts; resource_arguments = [ Proof_type_argument _ ]; _ };
   Proof_resource
     {
       resource_name = authority;
       resource_arguments = [ Proof_module_argument (Qid argument) ];
       _;
     };
   Proof_field { field_name; field_type = PTtyapp (_, [ _; _ ]) };
   Proof_function fn;
   Proof_lemma use;
  ] ->
      assert (facts.pid_str = "Facts");
      assert (authority.pid_str = "Authority");
      assert (argument.pid_str = "Facts");
      assert (field_name.pid_str = "facts");
      assert (fn.function_name.pid_str = "facts_of");
      assert (List.length fn.function_params = 1);
      begin match fn.function_body.term_desc with
      | Tcomprehension ((f, _), _) -> assert (f.pid_str = "f")
      | _ -> failwith "function comprehension was not parsed"
      end;
      begin match use.lemma_body.proof_desc with
      | Proof_let
          (_, { proof_desc = Proof_value { term_desc = Tcomprehension _; _ }; _ }, _) ->
          ()
      | _ -> failwith "proof comprehension was not parsed"
      end
  | _ -> failwith "unexpected resource declarations"
  end;
  begin match parse_proof "module Combined = Library.Product (First) (Second)" with
  | [
   Proof_resource
     {
       resource_functor = Qdot (Qid library, product);
       resource_arguments = [ Proof_module_argument _; Proof_module_argument _ ];
       _;
     };
  ] ->
      assert (library.pid_str = "Library");
      assert (product.pid_str = "Product")
  | _ -> failwith "generic proof module application was not parsed"
  end;
  begin match parse_proof "module Unlisted = NewFunctor (struct type t = int end)" with
  | [ Proof_resource { resource_functor = Qid name; _ } ] ->
      assert (name.pid_str = "NewFunctor")
  | _ -> failwith "proof module names were restricted by the parser"
  end;
  let rejected source =
    let lexbuf = Lexing.from_string source in
    match Spec_parser.proof Spec_lexer.token lexbuf with
    | _ -> failwith ("accepted malformed resource syntax: " ^ source)
    | exception Spec_parser.Error -> ()
    | exception Spec_ast.Syntax_error _ -> ()
  in
  begin match
    parse_proof
      {|module Job = Ghost.Task (struct let operation = Worker.run end)
        module Update = Ghost.AU (struct let operation = update end)|}
  with
  | [
   Proof_task { task_name; task_operation = Qdot (Qid worker, operation) };
   Proof_au { au_name; au_operation = Qid update };
  ] ->
      assert (task_name.pid_str = "Job");
      assert (worker.pid_str = "Worker");
      assert (operation.pid_str = "run");
      assert (au_name.pid_str = "Update");
      assert (update.pid_str = "update")
  | _ -> failwith "operation facades were not parsed"
  end;
  List.iter rejected
    [
      "module Job = Ghost.Task (struct let worker = run end)";
      "module Job = Other.Task (struct let operation = run end)";
      "module Update = Ghost.AU (struct let worker = update end)";
      "module Facts = SetRA (struct type element = int end)";
      "let facts : (int, Authority.t) Ghost.field = Other.field ()";
      "let facts : int = Ghost.field ()";
      "let facts_of x : int set = Set.empty";
      "let facts_of (x : int) = Set.empty";
      "let facts_of (x : int) : int set = Set.of_predicate (fun f -> f = x)";
      "lemma arbitrary_lambda = fun (x : int) -> x";
    ]

let () =
  let loop source = Spec_parser.loop_spec Spec_lexer.token (Lexing.from_string source) in
  let state = loop "invariant (fun saved -> saved = 0)" in
  assert (List.length state.state_invariants = 1);
  assert (state.invariants = []);
  let ordinary = loop "invariant true" in
  assert (ordinary.state_invariants = []);
  assert (List.length ordinary.invariants = 1);
  let fold = loop "invariant (fun (sum, count) remaining -> count >= 0)" in
  assert (List.length (fst (List.hd fold.state_invariants)) = 2);
  let saved = loop "invariant (fun accumulator remaining saved -> saved = 0)" in
  assert (List.length (fst (List.hd saved.state_invariants)) = 3)

let () =
  begin match
    parse_proof
      "invariant [@within Shared.Table.is_set s k'] tabled (s : t) (k' : int) (n : int) \
       = true"
  with
  | [
   Proof_invariant
     {
       inv_name = { pid_str = "tabled"; _ };
       inv_ancestry =
         Some
           {
             ancestry_target =
               Qdot
                 ( Qdot (Qid { pid_str = "Shared"; _ }, { pid_str = "Table"; _ }),
                   { pid_str = "is_set"; _ } );
             ancestry_args = [ { pid_str = "s"; _ }; { pid_str = "k'"; _ } ];
             _;
           };
       _;
     };
  ] ->
      ()
  | _ -> failwith "proof invariant parent was not parsed"
  end;
  begin match parse_proof "invariant [@within root] child (x : int) = true" with
  | [ Proof_invariant { inv_ancestry = Some { ancestry_args = []; _ }; _ } ] -> ()
  | _ -> failwith "invariant ancestry with zero arguments was not parsed"
  end;
  List.iter
    (fun (attribute, message) ->
      match parse_proof ("invariant " ^ attribute ^ " child (x : int) = true") with
      | exception Syntax_error (_, actual) when actual = message -> ()
      | _ -> failwith ("expected an invariant ancestry syntax error for " ^ attribute))
    [
      ("[@inline]", "An invariant's attribute is [@within ...]");
      ("[@parent root x]", "An invariant's attribute is [@within ...]");
      ("[@within]", "An invariant ancestry attribute needs a qualified invariant name");
      ( "[@within Shared..root]",
        "An invariant ancestry attribute needs a qualified invariant name" );
      ("[@within root x.field]", "Invariant ancestry arguments must be parameter names");
    ];
  begin match parse_invariant_declaration "invariant [@within root x] child (x : t)" with
  | exception
      Syntax_error (_, "Invariant ancestry is supported only on private proof definitions")
    ->
      ()
  | _ -> failwith "unchecked interface ancestry was accepted"
  end

let () =
  begin match
    parse_proof
      {|lemma inferred = ()
      lemma closed opens {} = ()
      lemma opened (x : int) opens { cell x _; Other.state; } = ()|}
  with
  | [ Proof_lemma inferred; Proof_lemma closed; Proof_lemma opened ] ->
      assert (inferred.lemma_opens = None);
      begin match closed.lemma_opens with
      | Some (_, []) -> ()
      | _ -> failwith "empty opens clause was not retained"
      end;
      begin match opened.lemma_opens with
      | Some (_, [ _; _ ]) -> ()
      | _ -> failwith "opens entries were not retained"
      end
  | _ -> failwith "unexpected opens declarations"
  end;
  begin match parse_proof "lemma repeated opens {} opens {} = ()" with
  | exception Syntax_error (_, "A lemma has at most one opens clause") -> ()
  | _ -> failwith "repeated opens clauses were accepted"
  end

let () =
  begin match parse_proof "lemma invalid opens { cell _ x } = ()" with
  | exception Syntax_error (_, "Wildcards in an opens entry must be trailing") -> ()
  | _ -> failwith "nontrailing opens wildcard was accepted"
  end

(* An auto lemma's postcondition carries alternative triggers, each of one or more terms. *)
let () =
  match
    parse_proof
      "lemma [@auto] l (x : int) ensures [f x | g x, h x]. (f x = g x) ensures (h x = 0) \
       = ()"
  with
  | [ Proof_lemma { lemma_ensures = [ ([ [ _ ]; [ _; _ ] ], _); ([], _) ]; _ } ] -> ()
  | _ -> failwith "lemma triggers were not parsed"

(* Brackets are triggers only before a dot, wherever whitespace falls; otherwise a list. *)
let () =
  begin match
    parse_proof "lemma [@auto] l (x : int list) ensures [f x] . f x === x = ()"
  with
  | [ Proof_lemma { lemma_ensures = [ ([ [ _ ] ], _) ]; _ } ] -> ()
  | _ -> failwith "spaced lemma trigger was not parsed"
  end;
  begin match parse_proof "lemma l (x : int list) ensures [x; x] === x @ x = ()" with
  | [ Proof_lemma { lemma_ensures = [ ([], _) ]; _ } ] -> ()
  | _ -> failwith "postcondition starting with a list literal was not parsed"
  end;
  begin match parse_proof "lemma [@auto] l (x : int) ensures [f x; g x]. f x = ()" with
  | exception Syntax_error (_, "Triggers are separated by , and alternatives by |") -> ()
  | _ -> failwith "semicolon between triggers was accepted"
  end;
  match parse_proof "lemma l (x : int) ensures [x, x] === [] = ()" with
  | exception Syntax_error (_, "A list literal separates its elements with ;") -> ()
  | _ -> failwith "comma in a list literal was accepted"

let () =
  begin match parse_proof "lemma typed opens {cell (_ : int)} = ()" with
  | [ Proof_lemma { lemma_opens = Some (_, [ entry ]); _ } ] ->
      begin match entry.term_desc with
      | Tapply (_, wildcard) -> assert (is_mask_wildcard wildcard)
      | _ -> failwith "typed mask selector was not parsed"
      end
  | _ -> failwith "typed mask selector was not retained"
  end;
  match parse_proof "lemma invalid (x : int) opens {cell (_ : int) x} = ()" with
  | exception Syntax_error (_, "Wildcards in an opens entry must be trailing") -> ()
  | _ -> failwith "nontrailing typed wildcard was accepted"
