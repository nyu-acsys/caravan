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

let manifest =
  let doc = "Print the tool version and compatibility information as JSON, then exit." in
  Arg.(value & flag & info [ "manifest" ] ~doc)

let lsp_mode =
  let doc = "Format error messages for LSP integration, as Raven does." in
  Arg.(value & flag & info [ "lsp-mode" ] ~doc)

let lsp_annotations =
  let doc =
    "With --lsp-mode, print an object with errors and source dependencies. Editor \
     annotation tables are currently empty."
  in
  Arg.(value & flag & info [ "lsp-annotations" ] ~doc)

let smt_timeout =
  let doc = "The time the solver may take on a query, in milliseconds." in
  Arg.(
    value
    & opt int Raven_api.default_options.smt_timeout
    & info [ "smt-timeout" ] ~docv:"MS" ~doc)

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

let main () no_greeting include_dirs history emit_rav manifest lsp_mode lsp_annotations
    smt_timeout files =
  if manifest then begin
    Logs.app (fun m ->
        m "%s"
          (Caravan_editor.Editor_report.manifest ~version:Caravan_config.version
             ~lsp_protocol:Caravan_config.lsp_protocol_version
             ~min_z3:Caravan_config.min_z3_version));
    0
  end
  else if lsp_mode && emit_rav then begin
    Logs.err (fun m -> m "--lsp-mode and --emit-rav cannot be used together");
    1
  end
  else if lsp_mode then (
    let results =
      List.map (Caravan_core.Check.run ~include_dirs ~history ~smt_timeout) files
    in
    Logs.app (fun m ->
        m "%s"
          (Caravan_editor.Editor_report.to_string ~annotations:lsp_annotations results));
    if List.for_all (fun result -> result.Caravan_core.Check.verified) results then 0
    else 1)
  else begin
    if not no_greeting then Logs.app (fun m -> m "%s" greeting);
    (* Every file is checked, also after one that fails. *)
    let results =
      List.map
        (Caravan_core.Check.file ~include_dirs ~history ~emit_rav ~smt_timeout)
        files
    in
    let verified = List.for_all Fun.id results in
    if verified then 0 else 1
  end

let cmd =
  let info = Cmd.info "caravan" ~version:Caravan_config.version in
  Cmd.v info
    Term.(
      const main $ setup $ no_greeting $ include_dirs $ history $ emit_rav $ manifest
      $ lsp_mode $ lsp_annotations $ smt_timeout $ files)

let () = Stdlib.exit (Cmd.eval' cmd)
