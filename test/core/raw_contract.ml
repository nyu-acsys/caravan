(** Boundary modes ignore spelling and preserve their runtime argument positions. *)

open Base
module R = Caravan_core.Raw_contract
module S = Caravan_spec.Spec_ast

let id ?(raw = false) name =
  S.mk_id ~loc:Location.none ~attrs:(if raw then [ "raw" ] else []) name

let header args result = Some S.{ hd_name = id "f"; hd_args = args; hd_ret = result }
let contract header = Some { S.empty_contract with header }
let check expected actual = R.check ~at:Location.none ~expected ~actual ()

let () =
  let ordinary = R.of_header None in
  let explicit = R.of_header (header [ Lvar (id "x"); Lunit Location.none ] []) in
  assert (not (R.any ordinary));
  assert (Result.is_ok (check ordinary explicit));
  let marked =
    R.of_contract
      (contract
         (header
            [
              Lghost (id "g", PTtyapp (Qid (id "int"), []));
              Lvar (id "x");
              Lvar (id ~raw:true "y");
            ]
            [ Lvar (id ~raw:true "result") ]))
  in
  assert (not (R.argument marked 0));
  assert (R.argument marked 1);
  assert (not (R.argument marked 2));
  assert marked.result;
  assert (R.any marked);
  assert (Result.is_error (check ordinary marked));
  assert (Result.is_error (check marked ordinary));
  let result_only = { marked with arguments = [] } in
  assert (Result.is_error (check ordinary result_only));
  assert (Result.is_ok (check result_only result_only))
