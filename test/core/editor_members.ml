open Base
module M = Caravan_core.Editor_members
module R = Raven_api

let at ?(file = "members.ml") first last =
  let position index =
    { Lexing.pos_fname = file; pos_cnum = index; pos_lnum = 1; pos_bol = 0 }
  in
  { Location.loc_start = position first; loc_end = position last; loc_ghost = false }

let member ?parent ?(group = false) name first last =
  M.make ?parent ~group ~name
    ~kind:(if group then "module" else "function")
    ~name_loc:(at first (first + 1))
    ~extent:(at first last) ()

let check name loc outcome : R.Progress.check =
  { name; kind = "proc"; loc = Caravan_core.Report.loc loc; outcome }

let project inventory checks =
  M.project inventory { R.Progress.phase = Progress; checks; diagnostics = [] }

let find members id =
  List.find_exn members ~f:(fun (member : M.member) -> String.equal member.id id)

let get = function
  | Ok result -> result
  | Error (error : Caravan_core.Report.error) -> failwith error.message

let () =
  Compmisc.init_path ();
  let lexbuf =
    Lexing.from_string
      "module Outer = struct module Inner = struct end end\n\
       module Make () = struct module Nested = struct end end"
  in
  Lexing.set_filename lexbuf "members.ml";
  let structure, environment =
    get
      (Caravan_core.Signature_contract.compiler ~at:Location.none (fun () ->
           let structure, _, _, _, environment =
             Typemod.type_structure (Compmisc.initial_env ())
               (Parse.implementation lexbuf)
           in
           (structure, environment)))
  in
  let proof =
    Caravan_spec.Spec_parser.proof Caravan_spec.Spec_lexer.token
      (Lexing.from_string
         "module Outer = struct module Inner = struct lemma keep = () end end\n\
          module Make () = struct module Nested = struct lemma keep = () end end")
  in
  let scopes =
    get (Caravan_core.Proof_scopes.resolve ~environment structure proof.declarations)
  in
  let bindings = M.runtime_modules ~parent:"root" structure in
  List.iter
    [ [ "Outer" ]; [ "Outer"; "Inner" ]; [ "Make" ]; [ "Make"; "Nested" ] ]
    ~f:(fun namespace ->
      let scope =
        Option.value_exn (Caravan_core.Proof_scopes.find_namespace scopes namespace)
      in
      let linked = Option.value_exn (M.runtime_module_for_scope bindings scope) in
      assert (String.equal linked.name (String.concat ~sep:"." namespace));
      let shifted = { scope with source_location = at ~file:"other.ml" 0 1 } in
      let linked_shifted =
        Option.value_exn (M.runtime_module_for_scope bindings shifted)
      in
      assert (String.equal linked.id linked_shifted.id))

let () =
  let root =
    M.make ~name:"members.ml" ~kind:"file" ~name_loc:(at 0 100) ~extent:(at 0 100)
      ~group:true ()
  in
  let outer = member ~parent:root.id ~group:true "Outer" 1 90 in
  let inner = member ~parent:outer.id ~group:true "Outer.Inner" 10 80 in
  let f = member ~parent:inner.id "Outer.Inner.f" 20 40 in
  let inventory = [ root; outer; inner; f ] in
  let first = check "Worker.f" (at 20 40) R.Progress.Verified in
  let second = check "Worker.f.helper" (at 30 31) R.Progress.Pending in
  let members = project inventory [ first; second ] in
  assert (Poly.equal (find members f.id).status M.Pending);
  assert (Poly.equal (find members outer.id).status M.Pending);
  assert (List.length (find members f.id).checks = 2);
  assert (Poly.equal (find members outer.id).counts [ (M.Pending, 1) ]);
  let failed = { second with outcome = R.Progress.Failed } in
  let members = project inventory [ first; failed; { failed with outcome = Verified } ] in
  assert (Poly.equal (find members f.id).status M.Failed);
  assert (List.length (find members f.id).checks = 2);
  let boundary = check "CheckedView.read" (at 10 80) R.Progress.Pending in
  let members = project inventory [ first; boundary ] in
  assert (Poly.equal (find members f.id).status M.Verified);
  assert (Poly.equal (find members inner.id).own_status M.Pending);
  assert (Poly.equal (find members outer.id).status M.Pending);
  assert (Poly.equal (find members outer.id).counts [ (M.Verified, 1) ]);
  let unknown = check "Dictionary.generated" (at ~file:"library.rav" 1 2) Verified in
  let members = project inventory [ unknown; first ] in
  assert (List.length (find members root.id).checks = 1);
  assert (Poly.equal (find members inner.id).status M.Verified);
  let module_check = { boundary with outcome = R.Progress.Verified } in
  let members =
    project inventory [ { unknown with outcome = Pending }; first; module_check ]
  in
  assert (Poly.equal (find members inner.id).status M.Pending);
  assert (Poly.equal (find members inner.id).own_status M.Verified);
  assert (Poly.equal (find members f.id).status M.Verified);
  assert (Poly.equal (find members inner.id).counts [ (M.Verified, 1) ]);
  let members = project inventory [ unknown; first; module_check ] in
  assert (Poly.equal (find members inner.id).status M.Verified);
  let members =
    project inventory [ { unknown with outcome = Failed }; first; module_check ]
  in
  assert (Poly.equal (find members inner.id).status M.Failed);
  assert (Poly.equal (find members f.id).status M.Verified);
  let ambiguous = { f with id = "ambiguous"; name = "Other.f" } in
  let members = project (ambiguous :: inventory) [ first ] in
  assert (List.is_empty (find members f.id).checks);
  assert (List.length (find members root.id).checks = 1);
  let cached = { first with outcome = R.Progress.Cached } in
  let members = project inventory [ cached; { first with name = "OtherWorker.f" } ] in
  assert (List.length (find members f.id).checks = 2);
  assert (Poly.equal (find members f.id).status M.Verified);
  let members = M.finish ~verified:false (project inventory [ first; second ]) in
  assert (Poly.equal (find members f.id).status M.Skipped);
  assert (Poly.equal (find members root.id).status M.Skipped);
  let members = M.finish ~verified:true (project inventory []) in
  assert (Poly.equal (find members f.id).status M.Checked);
  let independent = member ~parent:root.id ~group:true "Independent" 91 100 in
  let own = check "Independent.check" (at 91 100) R.Progress.Verified in
  let members =
    M.finish ~verified:false (project (independent :: inventory) [ first; failed; own ])
  in
  assert (Poly.equal (find members independent.id).status M.Verified)
