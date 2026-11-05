open Base
module Source = Caravan_core.Source
module S = Caravan_spec.Spec_ast

let () =
  Compmisc.init_path ();
  let environment = Compmisc.initial_env () in
  let libraries =
    match Source.standard_interfaces environment with
    | Ok libraries -> libraries
    | Error _ -> failwith "Cannot load standard-library contracts"
  in
  let library = List.hd_exn libraries in
  let lookup member =
    let mk_id = S.mk_id ~loc:Location.none in
    let q = S.Qdot (Qdot (Qid (mk_id "Stdlib"), mk_id "List"), mk_id member) in
    Source.value_path environment q
  in
  let reverse = Option.value_exn (lookup "rev") in
  assert (Path.same reverse (Path.Pdot (Pident library.library_id, "rev")));
  assert (Option.is_some (lookup "tl"));
  let parsed = Parse.interface (Lexing.from_string "val rev : bool -> bool") in
  let interface = { library.library with signature = parsed } in
  let actual = Env.find_module (Pident library.library_id) environment in
  match Mtype.scrape environment actual.md_type with
  | Mty_signature actual ->
      assert (Result.is_error (Source.check_interface environment actual interface))
  | Mty_ident _ | Mty_functor _ | Mty_alias _ -> assert false
