open Base

let () =
  let paths = Caravan_core.Source.library_files ~include_dirs:[] "client.ml" in
  assert (List.mem paths "./source_paths_fixture.mli" ~equal:String.equal);
  let own =
    Caravan_core.Source.library_files ~include_dirs:[] "source_paths_fixture.ml"
  in
  assert (not (List.mem own "./source_paths_fixture.mli" ~equal:String.equal))
