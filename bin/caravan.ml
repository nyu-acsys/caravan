(** The command line of Caravan. *)

open Cmdliner

let greeting =
  Printf.sprintf "Caravan version %s (raven-ivl.api version %d)" Caravan_config.version
    Raven_api.version

(* As Raven's: a level's name as the header, none for the application's messages. *)
let setup_logs style_renderer level =
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  let pp_h ppf style h = Fmt.pf ppf "[%a] " Fmt.(styled style string) h in
  let pp_header ppf (l, h) =
    let header default = Option.value h ~default in
    match l with
    | Logs.App ->
        Option.iter
          (fun h -> Fmt.pf ppf "[%a] " Fmt.(styled Logs_fmt.app_style string) h)
          h
    | Logs.Error -> pp_h ppf Logs_fmt.err_style (header "Error")
    | Logs.Warning -> pp_h ppf Logs_fmt.warn_style (header "Warning")
    | Logs.Info -> pp_h ppf Logs_fmt.info_style (header "Info")
    | Logs.Debug -> pp_h ppf Logs_fmt.debug_style (header "Debug")
  in
  Logs.set_reporter (Logs_fmt.reporter ~pp_header ())

let setup = Term.(const setup_logs $ Fmt_cli.style_renderer () $ Logs_cli.level ())

let no_greeting =
  let doc = "Do not print the greeting." in
  Arg.(value & flag & info [ "shh" ] ~doc)

let emit_rav =
  let doc = "Print the Raven program generated for the files instead of verifying it." in
  Arg.(value & flag & info [ "emit-rav" ] ~doc)

let check_stdlib =
  let doc = "Verify the bundled standard-library mathematical models and lemmas." in
  Arg.(value & flag & info [ "check-stdlib" ] ~doc)

let manifest =
  let doc = "Print the tool version and compatibility information as JSON, then exit." in
  Arg.(value & flag & info [ "manifest" ] ~doc)

let lsp_mode =
  let doc = "Format error messages for LSP integration, as Raven does." in
  Arg.(value & flag & info [ "lsp-mode" ] ~doc)

let lsp_annotations =
  let doc =
    "With --lsp-mode, print an object with errors, source dependencies, and editor \
     annotations."
  in
  Arg.(value & flag & info [ "lsp-annotations" ] ~doc)

let lsp_annotations_only =
  let doc =
    "With --lsp-mode --lsp-annotations, collect source annotations without translating \
     the program to Raven or verifying its proofs."
  in
  Arg.(value & flag & info [ "lsp-annotations-only" ] ~doc)

let smt_timeout =
  let doc = "The time the solver may take on a query, in milliseconds." in
  Arg.(
    value
    & opt int Raven_api.default_options.smt_timeout
    & info [ "smt-timeout" ] ~docv:"MS" ~doc)

let cache_dir =
  let doc = "Reuse successful verification results from the cache in $(docv)." in
  Arg.(value & opt (some string) None & info [ "cache-dir" ] ~docv:"DIR" ~doc)

let history =
  let doc =
    "How histories of states are encoded: $(b,sets), by the set of the states that the \
     current one extends, or $(b,monotone), by the current state, with lower bounds of \
     it as snapshots."
  in
  Arg.(
    value
    & opt (enum Caravan_core.History.encodings) Caravan_core.History.default
    & info [ "history" ] ~docv:"ENCODING" ~doc)

let include_dirs =
  let doc =
    "Look for libraries, interfaces without an implementation, also in $(docv), after \
     the file's own directory."
  in
  Arg.(value & opt_all dir [] & info [ "I" ] ~docv:"DIR" ~doc)

let files =
  let doc = "The OCaml files to verify." in
  Arg.(value & pos_all file [] & info [] ~docv:"FILE" ~doc)

let protocol_source = Logs.Src.create "caravan.editor"

module Protocol = (val Logs.src_log protocol_source)

let print text =
  Logs.Src.set_level protocol_source (Some Logs.App);
  Protocol.app (fun m -> m "%s" text)

let main ?on_progress ?(emit = print) () no_greeting include_dirs history emit_rav
    check_stdlib manifest lsp_mode lsp_annotations lsp_annotations_only smt_timeout
    cache_dir files =
  if manifest then begin
    emit
      (Caravan_editor.Editor_report.manifest ~version:Caravan_config.version
         ~lsp_protocol:Caravan_config.lsp_protocol_version
         ~min_z3:Caravan_config.min_z3_version);
    0
  end
  else if lsp_mode && emit_rav then begin
    Logs.err (fun m -> m "--lsp-mode and --emit-rav cannot be used together");
    1
  end
  else if check_stdlib && (lsp_mode || files <> []) then begin
    Logs.err (fun m ->
        m "--check-stdlib cannot be combined with --lsp-mode or source files");
    1
  end
  else if lsp_annotations_only && not (lsp_mode && lsp_annotations) then begin
    Logs.err (fun m -> m "--lsp-annotations-only requires --lsp-mode --lsp-annotations");
    1
  end
  else if lsp_mode then (
    let results =
      if lsp_annotations_only then
        List.map (Caravan_core.Check.annotations_only ~include_dirs) files
      else
        List.map
          (Caravan_core.Check.run ?cache_dir ?on_progress ~include_dirs ~history
             ~smt_timeout)
          files
    in
    emit (Caravan_editor.Editor_report.to_string ~annotations:lsp_annotations results);
    let succeeded result =
      if lsp_annotations_only then
        not
          (List.exists
             (fun (diagnostic : Raven_api.Diagnostic.t) ->
               diagnostic.severity = Raven_api.Diagnostic.Error)
             result.Caravan_core.Check.diagnostics)
      else result.Caravan_core.Check.verified
    in
    if List.for_all succeeded results then 0 else 1)
  else begin
    if not no_greeting then Logs.app (fun m -> m "%s" greeting);
    if check_stdlib then
      begin if
        Caravan_core.Check.standard_library ?cache_dir ~history ~emit_rav ~smt_timeout ()
      then 0
      else 1
      end
    else begin
      (* Every file is checked, also after one that fails. *)
      let results =
        List.map
          (Caravan_core.Check.file ?cache_dir ~include_dirs ~history ~emit_rav
             ~smt_timeout)
          files
      in
      let verified = List.for_all Fun.id results in
      if verified then 0 else 1
    end
  end

let cmd ?emit ?on_progress () =
  let info = Cmd.info "caravan" ~version:Caravan_config.version in
  Cmd.v info
    Term.(
      const (main ?emit ?on_progress)
      $ setup $ no_greeting $ include_dirs $ history $ emit_rav $ check_stdlib $ manifest
      $ lsp_mode $ lsp_annotations $ lsp_annotations_only $ smt_timeout $ cache_dir
      $ files)

let serve defaults =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.Src.set_level protocol_source (Some Logs.App);
  let answer fields = print (Yojson.Basic.to_string (`Assoc fields)) in
  let decode line =
    match Yojson.Basic.from_string line with
    | `Assoc fields ->
        let get key = List.assoc_opt key fields in
        begin match (get "id", get "cwd", get "args", get "partial") with
        | Some id, Some (`String cwd), Some (`List args), partial ->
            let strings =
              List.filter_map (function `String s -> Some s | _ -> None) args
            in
            if List.length strings <> List.length args then Error "args must be strings"
            else Ok (id, cwd, strings, partial = Some (`Bool true))
        | _ -> Error "Expected id, cwd, args and optional partial"
        end
    | _ -> Error "Expected a request object"
    | exception Yojson.Json_error message -> Error message
  in
  let rec loop () =
    match Stdio.In_channel.input_line Stdio.stdin with
    | None -> ()
    | Some line ->
        begin match decode line with
        | Error message -> answer [ ("id", `Null); ("error", `String message) ]
        | Ok (id, cwd, args, partial) ->
            if not (Sys.file_exists cwd && Sys.is_directory cwd) then
              answer [ ("id", id); ("error", `String ("No such directory: " ^ cwd)) ]
            else if not (List.mem "--lsp-mode" args && List.mem "--lsp-annotations" args)
            then
              answer
                [
                  ("id", id);
                  ("error", `String "Server requests require --lsp-mode --lsp-annotations");
                ]
            else begin
              Unix.chdir cwd;
              let output = Buffer.create 1024 and errors = Buffer.create 256 in
              let formatter = Format.formatter_of_buffer errors in
              let on_progress =
                if not partial then None
                else
                  Some
                    (fun (progress : Caravan_core.Check.progress) ->
                      let phase =
                        match progress.phase with
                        | Raven_api.Progress.Typed -> Some "typed"
                        | Scheduled -> Some "scheduled"
                        | Progress -> Some "progress"
                        | Final -> None
                      in
                      Option.iter
                        (fun phase ->
                          answer
                            [
                              ("id", id);
                              ("phase", `String phase);
                              ( "partial",
                                `String
                                  (Caravan_editor.Editor_report.to_string
                                     ~annotations:true [ progress.result ]) );
                            ])
                        phase)
              in
              let emit text =
                Buffer.add_string output text;
                Buffer.add_char output '\n'
              in
              let exit =
                Cmd.eval' ~help:formatter ~err:formatter
                  ~argv:(Array.of_list ("caravan" :: (defaults @ args)))
                  (cmd ~emit ?on_progress ())
              in
              Format.pp_print_flush formatter ();
              answer
                [
                  ("id", id);
                  ("exit", `Int exit);
                  ("stdout", `String (Buffer.contents output));
                  ("stderr", `String (Buffer.contents errors));
                ]
            end
        end;
        loop ()
  in
  loop ()

let () =
  let args = Array.to_list Sys.argv in
  match List.rev args with
  | "--server" :: defaults -> serve (List.tl (List.rev defaults))
  | _ -> Stdlib.exit (Cmd.eval' (cmd ()))
