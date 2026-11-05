open Base
module C = Caravan_core
module R = Raven_api

let get = function Ok value -> value | Error error -> failwith error.C.Report.message

let () =
  let source =
    get (C.Source.load ~check_standard_library:true "caravan/stdlib/check.ml")
  in
  let runtime_env = Compmisc.initial_env () in
  let bindings =
    List.filter source.spec_bindings ~f:(function
      | Types.Sig_module (id, _, _, _, _) ->
          not (String.equal (Ident.name id) "Stdlib_model")
      | _ -> true)
  in
  let env = C.Source.add_spec_bindings bindings runtime_env in
  let libraries =
    List.map source.libraries ~f:(fun library ->
        match library.library_proof with
        | None -> library
        | Some proof ->
            let text =
              proof.proof_text
              ^ "\n\
                 let zero (ignored : unit) : int = 0\n\n\
                 lemma zero_value (ignored : unit)\n\
                 ensures (zero () === 0) = ()\n"
            in
            let parsed = get (C.Source.parse_proof ~file:proof.proof_file text) in
            {
              library with
              library_proof =
                Some
                  {
                    proof with
                    proof_owner = None;
                    proof_text = text;
                    proof_declarations = parsed.declarations;
                  };
            })
  in
  let env, scopes, entries, libraries =
    get (C.Source.library_proof_scopes ~runtime_env env libraries)
  in
  let typed, _, _, _, _ = Typemod.type_structure env [] in
  let root = { source.proof_scopes.root with environment = env; structure = typed } in
  let user =
    get
      (C.Source.parse_proof ~file:"zero_client.proof"
         "lemma client_zero (ignored : unit)\n\
          ensures (Stdlib_model.List.zero () === 0) = ()\n")
  in
  let user_entries =
    List.map user.declarations ~f:(fun declaration ->
        let member = C.Proof_scopes.name declaration in
        C.Proof_scopes.
          {
            id = Ident.create_local member.pid_str;
            name = member;
            declaration;
            scope = root;
          })
  in
  let source =
    {
      source with
      typed;
      env;
      libraries;
      proof = user.declarations;
      proof_scopes =
        { root; scopes = scopes @ [ root ]; declarations = entries @ user_entries };
      spec_bindings = C.Source.specification_bindings runtime_env env;
    }
  in
  let program, _ = get (C.Translate.program source) in
  let result = R.verify program in
  if not result.verified then
    failwith
      (String.concat ~sep:"\n"
         (List.map result.diagnostics ~f:(fun d -> d.R.Diagnostic.message)))
