open Base
module C = Caravan_core
open C.Translate_context

let get = function
  | Ok value -> value
  | Error (error : C.Report.error) -> failwith error.message

let () =
  let id = Ident.create_local "integer" in
  let integer = Ctype.newconstr (Path.Pident id) [] in
  let alias_id = Ident.create_local "integer_alias" in
  let alias = Ctype.newconstr (Path.Pident alias_id) [] in
  let alias_data =
    {
      (C.Datatypes.logical_integer alias_id) with
      mathematical_integer = false;
      alias = Some integer;
    }
  in
  let given =
    declaration_inputs
      [ alias_data; C.Datatypes.logical_integer id ]
      ~shared:no_shared ~env:Env.empty ~preds:[] ~spec_funcs:[]
      ~proof_support:empty_proof_support ()
  in
  let open State.Syntax in
  let read field typ =
    State.ordinary_primitive given ~at:Location.none ~field typ C.Primitives.Read
  in
  let write typ =
    State.ordinary_primitive given ~at:Location.none ~field:"contents" typ
      C.Primitives.Write
  in
  let computation =
    let* first = read "A_B.x" Predef.type_int in
    let* second = read "A.B_x" Predef.type_int in
    let* repeat = read "A_B.x" Predef.type_int in
    let* bounded = write Predef.type_int in
    let* unbounded = write integer in
    let* alias_write = write alias in
    let+ bounded_again = write Predef.type_int in
    assert (not (String.equal first second));
    assert (String.equal first repeat);
    assert (not (String.equal bounded unbounded));
    assert (String.equal bounded bounded_again);
    assert (String.equal unbounded alias_write)
  in
  let (), state = get (State.run_from State.initial computation) in
  assert (List.length (State.primitives_in state.tables []) = 4)
