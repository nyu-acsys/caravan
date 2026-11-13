open Caravan_spec
open Spec_ast

let contract source = Spec_parser.contract Spec_lexer.token (Lexing.from_string source)
let proof source = Spec_parser.proof Spec_lexer.token (Lexing.from_string source)
let raw id = List.mem "raw" id.pid_attrs

let header source =
  match (contract source).header with Some header -> header | None -> assert false

let reject parser source =
  match parser source with
  | _ -> assert false
  | exception Syntax_error _ -> ()
  | exception Spec_parser.Error -> ()

let extracted_contract source =
  match (proof source).outlines with
  | [ { outline_contract = Some range; _ } ] ->
      let start = range.loc_start.pos_cnum in
      contract (String.sub source start (range.loc_end.pos_cnum - start))
  | _ -> assert false

let () =
  begin match header "(result [@raw]) = forward (value [@raw]) next" with
  | { hd_ret = [ Lvar result ]; hd_args = [ Lvar value; Lvar next ]; _ } ->
      assert (raw result && raw value && not (raw next))
  | _ -> assert false
  end;
  begin match header "(result [@raw], [token : int]) = forward (value [@raw])" with
  | { hd_ret = [ Lvar result; Lghost (token, _) ]; _ } ->
      assert (raw result && not (raw token))
  | _ -> assert false
  end;
  List.iter
    (fun source ->
      match (extracted_contract source).header with
      | Some { hd_ret = [ Lvar result ]; hd_args = [ Lvar value ]; _ } ->
          assert (raw result && raw value)
      | _ -> assert false)
    [
      "proof (result [@raw]) = forward (value [@raw]) = ()";
      "proof (result [@raw]) = forward (value [@raw]) requires (true) = ()";
    ];
  let with_clause =
    extracted_contract "proof (result [@raw]) = forward value ensures (true) = ()"
  in
  assert (List.length with_clause.ensures = 1);
  begin match (extracted_contract "proof forward (value [@raw]) = ()").header with
  | Some { hd_args = [ Lvar value ]; _ } -> assert (raw value)
  | _ -> assert false
  end;
  begin match
    (extracted_contract
       "proof result [@raw], [token : int] = forward (value [@raw]) ensures (true) = ()")
      .header
  with
  | Some { hd_ret = [ Lvar result; Lghost (_, _) ]; _ } -> assert (raw result)
  | _ -> assert false
  end;
  begin match header "(left, right) = pair value next" with
  | { hd_ret = [ Lvar left; Lvar right ]; _ } -> assert (not (raw left || raw right))
  | _ -> assert false
  end;
  begin match header "result = left + right" with
  | { hd_args = [ Lvar left; Lvar right ]; _ } -> assert (not (raw left || raw right))
  | _ -> assert false
  end;
  List.iter (reject contract)
    [
      "result = forward (value [@raw] [@raw])";
      "(result [@raw] [@raw]) = forward value";
      "result = forward (value [@implicit])";
      "result = forward (value [@raw 1])";
      "result = forward [value [@raw] : int]";
      "[result [@raw] : int] = forward value";
    ];
  reject proof
    "proof (forward [@raw]) value = at (value) (fun step -> let result = step () in \
     result)"
