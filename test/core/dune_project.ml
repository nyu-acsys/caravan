open Base
module D = Caravan_core.Dune_project

let a text = Sexp.Atom text
let l items = Sexp.List items
let f key value = l [ a key; value ]
let path value = l [ a value ]

let module_ ?(cmt = "") name ~impl ~intf =
  l
    [
      f "name" (a name);
      f "impl" (Option.value_map impl ~default:(l []) ~f:path);
      f "intf" (Option.value_map intf ~default:(l []) ~f:path);
      f "cmt" (if String.is_empty cmt then l [] else path cmt);
    ]

let library uid ~requires ~modules =
  l
    [
      a "library";
      l
        [
          f "name" (a uid);
          f "uid" (a uid);
          f "local" (a "true");
          f "requires" (l (List.map requires ~f:a));
          f "modules" (l modules);
        ];
    ]

let select entries =
  let root = Stdlib.Sys.getcwd () in
  let file = Unix.realpath (Stdlib.Filename.concat root "source_paths.ml") in
  D.select ~root ~file (l (f "build_context" (a "_build/default") :: entries))

let () =
  assert (
    String.equal
      (D.native_path ~windows:true "_build/default/lib/x.ml")
      "_build\\default\\lib\\x.ml");
  assert (D.path_equal ~windows:true "C:/Work/Api.mli" "c:\\work\\api.mli");
  assert (
    Option.equal String.equal
      (D.relative_to ~windows:true ~root:"C:\\" "c:/Work/Api.mli")
      (Some "Work\\Api.mli"));
  assert (
    Option.is_none (D.relative_to ~windows:true ~root:"C:\\work" "c:/workspace/Api.mli"));
  assert (Result.is_ok (D.parse_csexp "(3:foo(0:))"));
  assert (Result.is_error (D.parse_csexp "(3:fo)"));
  assert (Result.is_error (D.parse_csexp "999999999999999999:abc"));
  assert (Result.is_error (D.parse_csexp "(1:a)1:b"));
  let owner =
    library "owner" ~requires:[ "direct" ]
      ~modules:
        [
          module_ "Source_paths" ~impl:(Some "_build/default/source_paths.ml") ~intf:None;
        ]
  in
  let direct =
    library "direct" ~requires:[ "transitive" ]
      ~modules:
        [
          module_ "Backoff" ~impl:None
            ~intf:(Some "_build/default/../saturn/backoff/backoff.mli");
        ]
  in
  let transitive =
    library "transitive" ~requires:[]
      ~modules:
        [
          module_ "Source_paths_fixture" ~impl:None
            ~intf:(Some "_build/default/source_paths_fixture.mli");
        ]
  in
  let unrelated =
    library "unrelated" ~requires:[]
      ~modules:
        [
          module_ "Treiber_stack" ~impl:None
            ~intf:(Some "_build/default/../saturn/treiber_stack/treiber_stack.mli");
        ]
  in
  let expected =
    [
      Unix.realpath
        (Stdlib.Filename.concat (Stdlib.Sys.getcwd ()) "source_paths_fixture.mli");
      Unix.realpath
        (Stdlib.Filename.concat (Stdlib.Sys.getcwd ()) "../saturn/backoff/backoff.mli");
    ]
  in
  begin match select [ owner; direct; transitive; unrelated ] with
  | Ok actual when List.equal String.equal actual expected -> ()
  | Ok actual -> failwith ("unexpected interfaces: " ^ String.concat ~sep:", " actual)
  | Error message -> failwith message
  end;
  assert (
    Result.equal (List.equal String.equal) String.equal (select [ unrelated ]) (Ok []));
  assert (Result.is_error (select [ owner; owner ]));
  let collision =
    library "transitive" ~requires:[]
      ~modules:
        [
          module_ "Backoff" ~impl:None
            ~intf:(Some "_build/default/../translate/libraries/include_dirs/backoff.mli");
        ]
  in
  begin match select [ owner; direct; collision ] with
  | Error message -> assert (String.is_substring message ~substring:"Backoff")
  | Ok _ -> assert false
  end;
  let own_api =
    library "own" ~requires:[ "direct" ]
      ~modules:
        [
          module_ "Treiber_stack"
            ~impl:(Some "_build/default/../saturn/treiber_stack/treiber_stack.ml")
            ~intf:(Some "_build/default/../saturn/treiber_stack/treiber_stack.mli");
        ]
  in
  let own_file =
    Unix.realpath
      (Stdlib.Filename.concat (Stdlib.Sys.getcwd ())
         "../saturn/treiber_stack/treiber_stack.ml")
  in
  assert (
    Result.equal (List.equal String.equal) String.equal
      (D.select ~root:(Stdlib.Sys.getcwd ()) ~file:own_file
         (l [ f "build_context" (a "_build/default"); own_api; direct; transitive ]))
      (Ok expected));
  let stale =
    library "direct" ~requires:[]
      ~modules:
        [ module_ "Absent" ~impl:None ~intf:(Some "_build/default/absent_generated.mli") ]
  in
  assert (
    Result.equal (List.equal String.equal) String.equal (select [ owner; stale ]) (Ok []));
  let wrapped =
    library "direct" ~requires:[]
      ~modules:
        [
          module_ "Source_paths_fixture"
            ~cmt:"_build/default/.direct.objs/byte/direct__Source_paths_fixture.cmt"
            ~impl:None ~intf:(Some "_build/default/source_paths_fixture.mli");
        ]
  in
  assert (Result.is_error (select [ owner; wrapped ]));
  let camel_case =
    library "direct" ~requires:[]
      ~modules:
        [
          module_ "SourcePathsFixture"
            ~cmt:"_build/default/.direct.objs/byte/sourcePathsFixture.cmt" ~impl:None
            ~intf:(Some "_build/default/source_paths_fixture.mli");
        ]
  in
  assert (Result.is_ok (select [ owner; camel_case ]))
