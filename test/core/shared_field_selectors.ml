open Base
module C = Caravan_core
module S = Caravan_spec.Spec_ast
module Fields = C.Access_fields

let get = function
  | Ok value -> value
  | Error (error : C.Report.error) -> failwith error.message

let typed source =
  Compmisc.init_path ();
  get
    (C.Signature_contract.compiler ~at:Location.none (fun () ->
         let parsed = Parse.implementation (Lexing.from_string source) in
         let _, _, _, _, environment =
           Typemod.type_structure (Compmisc.initial_env ()) parsed
         in
         environment))

let resolve environment source =
  let parsed =
    Caravan_spec.Spec_parser.proof Caravan_spec.Spec_lexer.token
      (Lexing.from_string source)
  in
  match parsed.declarations with
  | [ S.Proof_access_field { access_name; access_kind; access_owner; access_selector } ]
    ->
      Fields.resolve ~environment ~name:access_name ~kind:access_kind ~owner:access_owner
        ~selector:access_selector ~core_type:C.Source_core.core_type
  | _ -> failwith "Expected one shared-field facade"

let field environment facade owner selector =
  resolve environment
    (Printf.sprintf "module Selected = Ghost.%s (struct let field (n : %s) = %s end)"
       facade owner selector)

let same_type environment left right =
  get
    (C.Signature_contract.compiler ~at:Location.none (fun () ->
         Ctype.is_equal environment false [ left ] [ right ]))

let rejects expected = function
  | Ok _ -> failwith "Expected a shared-field error"
  | Error (error : C.Report.error) ->
      assert (String.is_substring error.message ~substring:expected)

let () =
  let environment =
    typed
      {|type node = { mutable counter : int; mutable capacity : int; readonly : bool }
        type other = { mutable counter : bool }
        type alias = node
        type 'a box = { mutable contents : 'a }
        module Original = struct type t = { mutable counter : int } end
        module Alias = Original
        type imported = Original.t|}
  in
  let counter = get (field environment "Frozen" "node" "n.counter") in
  let capacity = get (field environment "Relaxed" "node" "n.capacity") in
  let unrelated = get (field environment "Frozen" "other" "n.counter") in
  assert (same_type environment counter.value_type Predef.type_int);
  assert (same_type environment unrelated.value_type Predef.type_bool);
  assert (String.equal counter.label.lbl_name "counter");
  assert (not (Fields.same_field counter unrelated));
  assert (not (Fields.same_field counter capacity));
  get (Fields.validate_registry [ counter; capacity; unrelated ]);
  let alias = get (field environment "Frozen" "alias" "n.counter") in
  assert (Fields.same_field counter alias);
  assert (same_type environment counter.owner_type alias.owner_type);
  let original = get (field environment "Frozen" "Original.t" "n.counter") in
  let module_alias = get (field environment "Frozen" "Alias.t" "n.counter") in
  let imported = get (field environment "Frozen" "imported" "n.counter") in
  assert (Fields.same_field original module_alias);
  assert (Fields.same_field original imported);
  assert (not (Fields.same_field original counter));
  let boxed_int = get (field environment "Relaxed" "int box" "n.contents") in
  let boxed_bool = get (field environment "Relaxed" "bool box" "n.contents") in
  assert (same_type environment boxed_int.value_type Predef.type_int);
  assert (same_type environment boxed_bool.value_type Predef.type_bool);
  assert (Fields.same_field boxed_int boxed_bool);
  get (Fields.validate_registry [ counter; alias ]);
  let conflicting = get (field environment "Relaxed" "alias" "n.counter") in
  rejects "cannot use both" (Fields.validate_registry [ counter; conflicting ]);
  rejects "mutable field" (field environment "Frozen" "node" "n.readonly");
  assert (Result.is_error (field environment "Frozen" "node" "n.missing"));
  rejects "directly select" (field environment "Frozen" "node" "n.counter + 1");
  rejects "directly select" (field environment "Frozen" "node" "other.counter");
  let generic = get (field environment "Relaxed" "'a box" "n.contents") in
  assert (
    not
      (List.is_empty (Ctype.free_variables_list ~env:environment [ generic.value_type ])))

let () =
  let environment =
    typed
      {|type (_, _) node =
          | Null : ('a, [ `Null ]) node
          | Node : { mutable counter : int; mutable capacity : int; mutable value : 'a }
              -> ('a, [ `Node ]) node
        type _ choice =
          | Left : { mutable counter : int } -> [ `Left ] choice
          | Right : { mutable counter : int } -> [ `Right ] choice
        type alias = (int, [ `Node ]) node|}
  in
  let counter =
    get
      (resolve environment
         {|module Counter = Ghost.Frozen (struct
             let field (Node r : (_, [< `Node]) node) = r.counter
           end)|})
  in
  let alias =
    get
      (resolve environment
         {|module CounterAlias = Ghost.Frozen (struct
             let field (Node r : alias) = r.counter
           end)|})
  in
  assert (same_type environment counter.value_type Predef.type_int);
  assert (Fields.same_field counter alias);
  let value =
    get
      (resolve environment
         {|module Value = Ghost.Relaxed (struct
             let field (Node r : (bool, [< `Node]) node) = r.value
           end)|})
  in
  assert (same_type environment value.value_type Predef.type_bool);
  assert (not (Fields.same_field counter value));
  let variant constructor =
    get
      (resolve environment
         (Printf.sprintf
            "module Counter = Ghost.Frozen (struct let field (%s r : [< `%s] choice) = \
             r.counter end)"
            constructor constructor))
  in
  assert (not (Fields.same_field (variant "Left") (variant "Right")));
  get (Fields.validate_registry [ counter; alias ]);
  let conflicting =
    get
      (resolve environment
         {|module Capacity = Ghost.Relaxed (struct
             let field (Node r : alias) = r.counter
           end)|})
  in
  rejects "cannot use both" (Fields.validate_registry [ counter; conflicting ]);
  rejects "directly select"
    (resolve environment
       {|module Counter = Ghost.Frozen (struct
           let field (Node r : (_, [< `Node]) node) = n.counter
         end)|})

let () =
  let source = get (C.Source.load "shared_fields_fixture.ml") in
  let fields = source.C.Source.proof_access_fields in
  assert (List.length fields = 3);
  let counter =
    List.find_exn fields ~f:(fun field ->
        String.equal field.Fields.name.pid_str "Counter")
  in
  let value =
    List.find_exn fields ~f:(fun field -> String.equal field.Fields.name.pid_str "Value")
  in
  let inline_counter =
    List.find_exn fields ~f:(fun field ->
        String.equal field.Fields.name.pid_str "NodeCounter")
  in
  assert (Poly.equal counter.kind S.Frozen);
  assert (Poly.equal value.kind S.Relaxed);
  assert (same_type source.env counter.value_type Predef.type_int);
  assert (same_type source.env value.value_type Predef.type_bool);
  assert (not (Fields.same_field counter value));
  assert (same_type source.env inline_counter.value_type Predef.type_int);
  assert (not (Fields.same_field counter inline_counter));
  let _ = get (C.Translate.program source) in
  ()

let () =
  let rejected file expected =
    match C.Source.load file with
    | Ok _ -> failwith "Accepted incompatible aliases of a shared-field facade"
    | Error error ->
        assert (String.is_substring error.message ~substring:expected);
        begin match error.related with
        | [ (previous, _) ] ->
            assert (
              String.equal previous.loc_start.pos_fname error.loc.loc_start.pos_fname);
            assert (previous.loc_start.pos_cnum < error.loc.loc_start.pos_cnum)
        | _ -> failwith "Expected the first field facade as a related location"
        end
  in
  rejected "shared_fields_alias_conflict_fixture.ml" "cannot use both";
  let aliases = get (C.Source.load "shared_fields_alias_duplicate_fixture.ml") in
  match aliases.C.Source.proof_access_fields with
  | [ first; second ] -> assert (Fields.same_field first second)
  | _ -> failwith "Expected compatible facade aliases"

let () =
  let source = get (C.Source.load "../translate/field_disciplines/partial.ml") in
  let scopes = get (C.Program_scopes.run source) in
  match scopes.source.proof_access_fields with
  | [ original; reexported ] -> assert (Fields.same_field original reexported)
  | _ -> failwith "Expected the original and re-exported field facades"
