open Caravan_spec
open Spec_ast

let contract source = Spec_parser.contract Spec_lexer.token (Lexing.from_string source)

let extracted source =
  let proof = Spec_parser.proof Spec_lexer.token (Lexing.from_string source) in
  match proof.outlines with
  | [ { outline_contract = Some range; _ } ] ->
      let start = range.loc_start.pos_cnum in
      contract (String.sub source start (range.loc_end.pos_cnum - start))
  | _ -> assert false

let reject source =
  match contract source with
  | _ -> assert false
  | exception Syntax_error _ -> ()
  | exception Spec_parser.Error -> ()

let () =
  assert ((contract "result = read cell").opens = None);
  List.iter
    (fun parse ->
      begin match (parse "result = read cell opens {} requires (true)").opens with
      | Some (_, []) -> ()
      | _ -> assert false
      end;
      begin match
        (parse
           "result = read cell opens {live cell _; Value.frozen cell; Value.frozen} \
            ensures (true)")
          .opens
      with
      | Some (_, [ _; _; _ ]) -> ()
      | _ -> assert false
      end)
    [ contract; (fun source -> extracted ("proof " ^ source ^ " = ()")) ];
  List.iter reject
    [
      "result = read cell opens {} opens {}";
      "result = read cell opens {live _ cell}";
      "result = read cell opens live cell";
    ]
