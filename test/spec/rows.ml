open Caravan_spec
open Spec_ast

let parse_type source =
  let lexbuf = Lexing.from_string ("type parsed = " ^ source) in
  let proof = Spec_parser.proof Spec_lexer.token lexbuf in
  match proof.declarations with
  | [ Proof_type { type_kind = Alias typ; _ } ] -> typ
  | _ -> failwith "Expected one type alias"

let row expected_bound expected_tags source =
  match parse_type source with
  | PTvariant (bound, tags) ->
      assert (bound = expected_bound);
      assert (List.map (fun tag -> tag.pid_str) tags = expected_tags)
  | _ -> failwith "Expected a polymorphic-variant row"

let () =
  row Closed_row [ "Node" ] "[ `Node ]";
  row Closed_row [ "Null"; "Node" ] "[ `Null | `Node ]";
  row Lower_row [ "Node" ] "[> `Node ]";
  row Upper_row [ "Node" ] "[< `Node ]";
  row Closed_row [ "node" ] "[ `node ]";
  begin match parse_type "('a, [ `Node ]) node" with
  | PTtyapp (Qid { pid_str = "node"; _ }, [ PTtyvar _; PTvariant (Closed_row, [ _ ]) ]) ->
      ()
  | _ -> failwith "Expected a row in an indexed type application"
  end;
  begin match parse_type "[ `Node ] -> [< `Null | `Node ]" with
  | PTarrow (PTvariant (Closed_row, [ _ ]), PTvariant (Upper_row, [ _; _ ])) -> ()
  | _ -> failwith "Expected row argument and result types"
  end;
  begin match Spec_lexer.token (Lexing.from_string "`max`") with
  | Spec_parser.BACKQUOTE_LIDENT "max" -> ()
  | _ -> failwith "Backquoted infix syntax changed"
  end;
  begin match parse_type "[ `Node of int ]" with
  | _ -> failwith "Accepted a payload-bearing polymorphic-variant tag"
  | exception Syntax_error (_, message) ->
      assert (String.starts_with ~prefix:"Polymorphic-variant type indices" message)
  end;
  begin match parse_type "[>= `Node ]" with
  | _ -> failwith "Accepted an invalid row bound"
  | exception Syntax_error _ -> ()
  end
