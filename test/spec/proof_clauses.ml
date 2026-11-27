open Caravan_spec
open Spec_ast

let proof source = Spec_parser.proof Spec_lexer.token (Lexing.from_string source)
let contract source = Spec_parser.contract Spec_lexer.token (Lexing.from_string source)

let extracted source =
  match (proof source).outlines with
  | [ { outline_contract = Some range; _ } ] ->
      let first = range.loc_start.pos_cnum in
      String.sub source first (range.loc_end.pos_cnum - first)
  | _ -> failwith "missing proof contract"

let lemma source =
  match (proof source).declarations with
  | [ Proof_lemma { lemma_requires; lemma_ensures; lemma_body; _ } ] ->
      (lemma_requires, List.map snd lemma_ensures, lemma_body)
  | _ -> failwith "missing lemma"

let () =
  List.iter
    (fun header ->
      List.iter
        (fun body ->
          let text = extracted ("proof " ^ header ^ " = " ^ body) in
          assert (text = header);
          ignore (contract text))
        [ "()"; "on return begin assert x = y end" ])
    [
      "result = f x requires x >= 0 ensures result === x";
      "result = f x atomic requires own x value atomic ensures own x value";
      "result = f x raises Failed value -> value === x";
      "result = f x raises Failed atomic raises Failed value -> value === x";
      "result = f x ensures forall value : int. value >= 0 -> result === x";
      "result = f x ensures match result with Some value -> value === x | None -> true";
      "result = f x ensures if x = y then result = x else result === y";
      "result = f x ensures let same = x = y in same || result === x";
      "result = f x ensures (result = x) && x >= 0";
      "result = f x requires (x = y) ensures (result = x)";
      "result, [event : int] = f x ensures result === x && event >= 0";
      "f x requires x <> y ensures true";
    ];
  let _, equal_ensures, equal_body =
    lemma "lemma equal (x : int) ensures x === x = x = x"
  in
  begin match (List.hd equal_ensures).term_desc with
  | Tinfix (_, { pid_str = "==="; _ }, _) -> ()
  | _ -> failwith "clause equality was lost"
  end;
  begin match equal_body.proof_desc with
  | Proof_value { term_desc = Tinfix (_, { pid_str = "="; _ }, _); _ } -> ()
  | _ -> failwith "proof-body equality was consumed by the clause"
  end;
  let grouped_requires, _, _ =
    lemma "lemma equal (x : int) requires (x = x) ensures true = ()"
  in
  begin match (chain (List.hd grouped_requires)).term_desc with
  | Tapply
      ( { term_desc = Tapply ({ term_desc = Tvar (Qid { pid_str = "="; _ }); _ }, _); _ },
        _ ) ->
      ()
  | _ -> failwith "parenthesized structural equality was lost"
  end;
  List.iter
    (fun clause ->
      let requires, ensures, body =
        lemma ("lemma test (x : int) " ^ clause ^ " = assert x = x")
      in
      assert (List.length requires = 1);
      assert (List.length ensures = 1);
      begin match body.proof_desc with
      | Proof_assert { term_desc = Tinfix (_, { pid_str = "="; _ }, _); _ } -> ()
      | _ -> failwith "proof-body assertion changed"
      end)
    [
      "requires x >= 0 ensures x === x";
      "requires (x >= 0) ensures (x === x)";
      "requires true ensures forall value : int. value === value";
      "requires true ensures match x with 0 -> true | _ -> x > 0";
      "requires true ensures if x = 0 then x = 0 else x <> 0";
      "requires true ensures let same = x = x in same";
      "requires true ensures not false && old x === x";
      "requires true ensures (x === x : bool)";
    ]
