open Caravan_spec
open Spec_ast

let parse_proof source =
  let lexbuf = Lexing.from_string source in
  try Spec_parser.proof Spec_lexer.token lexbuf
  with Spec_parser.Error ->
    failwith
      (Printf.sprintf "proof syntax error at %d (%S)" (Lexing.lexeme_start lexbuf)
         (Lexing.lexeme lexbuf))

let parse_ghost source =
  let lexbuf = Lexing.from_string source in
  Spec_parser.ghost_stmts Spec_lexer.token lexbuf

let rec proof_kinds expr =
  match expr.proof_desc with
  | Proof_value _ -> [ "value" ]
  | Proof_let (_, value, body) -> ("let" :: proof_kinds value) @ proof_kinds body
  | Proof_seq (a, b) -> ("seq" :: proof_kinds a) @ proof_kinds b
  | Proof_if (_, yes, no) -> ("if" :: proof_kinds yes) @ proof_kinds no
  | Proof_match (_, cases) ->
      "match" :: List.concat_map (fun (_, body) -> proof_kinds body) cases
  | Proof_assert _ -> [ "assert" ]
  | Proof_fold (_, witnesses) ->
      [ (if witnesses = [] then "fold" else "fold with witnesses") ]
  | Proof_unfold (_, names) -> [ (if names = [] then "unfold" else "unfold with names") ]

let () =
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
        action dec = (* an action comment *) { s with count = s.count - 1 }|}
  with
  | [
   Proof_type { type_name; type_ctors = [ (linked, args); (empty, []) ] };
   Proof_state _;
   Proof_action _;
  ] ->
      assert (type_name.pid_str = "link");
      assert (linked.pid_str = "Linked");
      assert (List.length args = 3);
      assert (empty.pid_str = "Empty")
  | _ -> failwith "unexpected logical type or state declarations"
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
  List.iter rejected
    [
      "module Facts = SetRA (struct type element = int end)";
      "let facts : (int, Authority.t) Ghost.field = Other.field ()";
      "let facts : int = Ghost.field ()";
      "let facts_of x : int set = Set.empty";
      "let facts_of (x : int) = Set.empty";
      "let facts_of (x : int) : int set = Set.of_predicate (fun f -> f = x)";
      "lemma arbitrary_lambda = fun (x : int) -> x";
    ]
