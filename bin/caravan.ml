(** The command line of Caravan. *)

open Cmdliner

let greeting =
  Printf.sprintf "Caravan version %s (raven.api version %d)" Caravan_config.version
    Raven_api.version

let setup_logs style_renderer level =
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  Logs.set_reporter (Logs_fmt.reporter ())

let setup = Term.(const setup_logs $ Fmt_cli.style_renderer () $ Logs_cli.level ())

let no_greeting =
  let doc = "Do not print the greeting." in
  Arg.(value & flag & info [ "shh" ] ~doc)

let files =
  let doc = "The OCaml files to verify." in
  Arg.(value & pos_all file [] & info [] ~docv:"FILE" ~doc)

let main () no_greeting files =
  if not no_greeting then Logs.app (fun m -> m "%s" greeting);
  if not (List.is_empty files) then
    Logs.err (fun m -> m "Verifying OCaml files is not implemented yet.");
  if List.is_empty files then 0 else 1

let cmd =
  let info = Cmd.info "caravan" ~version:Caravan_config.version in
  Cmd.v info Term.(const main $ setup $ no_greeting $ files)

let () = Stdlib.exit (Cmd.eval' cmd)
