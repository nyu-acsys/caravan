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
  assert (List.length (State.primitives_in state.tables []) = 4);
  let requests =
    [
      read "A_B.x" Predef.type_int;
      read "A.B_x" Predef.type_int;
      write Predef.type_int;
      write integer;
    ]
  in
  let names requests =
    fst (get (State.run_from State.initial (State.all requests ~f:State.in_procedure)))
  in
  assert (List.equal String.equal (names requests) (List.rev (names (List.rev requests))));
  let instance target dictionaries = State.instance_given given ~target ~dictionaries in
  let requests =
    [
      instance "A_B.x" [ "Values.Int" ];
      instance "A.B_x" [ "Values.Int" ];
      instance "Worker" [ "A.B"; "C" ];
      instance "Worker" [ "A"; "B.C" ];
    ]
  in
  let first = names requests in
  assert (List.equal String.equal first (List.rev (names (List.rev requests))));
  assert (List.length (List.dedup_and_sort first ~compare:String.compare) = 4);
  let repeated, _ =
    get
      (State.run_from State.initial
         (State.all (requests @ requests) ~f:State.in_procedure))
  in
  assert (List.equal String.equal repeated (first @ first))

let () =
  let module Names = C.Fresh_names in
  let allocate keys =
    Names.reset ();
    List.map keys ~f:(fun key -> Names.for_key ~key "Values$Shared")
  in
  let keys = [ "first"; "second"; "first"; "third" ] in
  let forward = allocate keys in
  assert (List.equal String.equal forward (List.rev (allocate (List.rev keys))));
  assert (List.length (List.dedup_and_sort forward ~compare:String.compare) = 3);
  let reserved = Names.for_key ~key:"reserved" "Values$Shared" in
  Names.reset ();
  Names.reserve [ reserved ];
  match Names.for_key ~key:"reserved" "Values$Shared" with
  | exception Failure _ -> ()
  | _ -> failwith "A reserved structural name must abort rather than change with order"
