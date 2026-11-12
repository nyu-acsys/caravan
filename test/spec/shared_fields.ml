open Caravan_spec
open Spec_ast

let parse source =
  let lexbuf = Lexing.from_string source in
  (Spec_parser.proof Spec_lexer.token lexbuf).declarations

let field expected_kind expected_module expected_type expected_label source =
  match parse source with
  | [ Proof_access_field { access_name; access_kind; access_owner; access_selector } ] ->
      assert (access_kind = expected_kind);
      assert (access_name.pid_str = expected_module);
      begin match access_owner with
      | { pat_desc = Pid owner; _ }, PTtyapp (Qid typ, []) ->
          assert (owner.pid_str = "n");
          assert (typ.pid_str = expected_type)
      | _ -> failwith "Expected a typed owner"
      end;
      begin match access_selector.term_desc with
      | Tfield ({ term_desc = Tvar (Qid owner); _ }, Qid label) ->
          assert (owner.pid_str = "n");
          assert (label.pid_str = expected_label)
      | _ -> failwith "Expected a field selector"
      end
  | _ -> failwith "Expected one shared-field facade"

let rejected expected source =
  match parse source with
  | _ -> failwith "Accepted an invalid shared-field facade"
  | exception Syntax_error (_, message) -> assert (message = expected)

let () =
  field Frozen "Counter" "node" "counter"
    "module Counter = Ghost.Frozen (struct let field (n : node) = n.counter end)";
  field Relaxed "Capacity" "node" "capacity"
    "module Capacity = Ghost.Relaxed (struct let field (n : node) = n.capacity end)";
  begin match
    parse
      {|module Proof = struct
          module Counter = Ghost.Frozen (struct
            let field (n : int node) = n.counter
          end)
        end|}
  with
  | [ Proof_module { module_declarations = [ Proof_access_field field ]; _ } ] ->
      begin match field.access_owner with
      | _, PTtyapp (Qid { pid_str = "node"; _ }, [ PTtyapp (Qid int, []) ]) ->
          assert (int.pid_str = "int")
      | _ -> failwith "Expected a parameterized owner type"
      end
  | _ -> failwith "Expected a nested shared-field facade"
  end;
  begin match
    parse
      {|module Counter = Ghost.Frozen (struct
          let field (Node r : (_, [< `Node]) node) = r.counter
        end)|}
  with
  | [
   Proof_access_field
     {
       access_owner =
         ( { pat_desc = Pconstr (Qid constructor, Some { pat_desc = Pid owner; _ }); _ },
           PTtyapp (Qid node, [ PTtyany; PTvariant (Upper_row, [ tag ]) ]) );
       access_selector =
         { term_desc = Tfield ({ term_desc = Tvar (Qid selected); _ }, Qid label); _ };
       _;
     };
  ] ->
      assert (constructor.pid_str = "Node");
      assert (owner.pid_str = "r");
      assert (selected.pid_str = "r");
      assert (label.pid_str = "counter");
      assert (node.pid_str = "node");
      assert (tag.pid_str = "Node")
  | _ -> failwith "Expected a constructor-record field selector"
  end;
  rejected "A shared-field facade argument must define field"
    "module Counter = Ghost.Frozen (struct let selector (n : node) = n.counter end)";
  rejected "Ghost.History has been renamed to Ghost.Relaxed"
    "module Capacity = Ghost.History (struct let field (n : node) = n.capacity end)";
  rejected "Expected Ghost.Frozen or Ghost.Relaxed"
    "module Counter = Other.Frozen (struct let field (n : node) = n.counter end)";
  begin match
    parse "module Counter = Ghost.Frozen (struct let field n = n.counter end)"
  with
  | _ -> failwith "Accepted an untyped field owner"
  | exception Spec_parser.Error -> ()
  | exception Syntax_error _ -> ()
  end

let () =
  let scope source = Spec_parser.scope Spec_lexer.token (Lexing.from_string source) in
  let plain = scope "Ghost.scope (fun read -> let result = read () in result)" in
  let frozen = scope "Ghost.frozen_scope (fun read -> let result = read () in result)" in
  assert (plain.scope_mode = General_scope);
  assert (frozen.scope_mode = Frozen_scope);
  assert (frozen.scope_state = None);
  let published =
    scope "Ghost.published_scope (fun read -> let result = read () in result)"
  in
  assert (published.scope_mode = Published_scope);
  let stateful =
    scope
      "Ghost.State.frozen_scope (fun read () -> let result = read () in (result, result))"
  in
  assert (stateful.scope_mode = Frozen_scope);
  assert (Option.is_some stateful.scope_state)
