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

let smt_timeout =
  let doc = "The time the solver may take on a query, in milliseconds." in
  Arg.(
    value
    & opt int Raven_api.default_options.smt_timeout
    & info [ "smt-timeout" ] ~docv:"MS" ~doc)

let files =
  let doc = "The OCaml files to verify." in
  Arg.(value & pos_all file [] & info [] ~docv:"FILE" ~doc)

let main () no_greeting emit_rav smt_timeout files =
  if not no_greeting then Logs.app (fun m -> m "%s" greeting);
  (* Every file is checked, also after one that fails. *)
  let results = List.map (Caravan_core.Check.file ~emit_rav ~smt_timeout) files in
  let verified = List.for_all Fun.id results in
  if verified then 0 else 1

let cmd =
  let info = Cmd.info "caravan" ~version:Caravan_config.version in
  Cmd.v info Term.(const main $ setup $ no_greeting $ emit_rav $ smt_timeout $ files)

let () = Stdlib.exit (Cmd.eval' cmd)
