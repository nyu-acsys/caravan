(** Verifying OCaml files: reading, translating, and verifying with Raven. *)

open Base
module R = Raven_api

(** Verifies [file]; whether it verified. With [emit_rav], the Raven program is printed
    instead. *)
let file ~(emit_rav : bool) (file : string) : bool =
  match Source.load file with
  | Error error ->
      Report.print error;
      false
  | Ok source -> (
      match Translate.program source with
      | Error error ->
          Report.print error;
          false
      | Ok program when emit_rav ->
          Logs.app (fun m -> m "%s" (R.Program.to_string program));
          true
      | Ok program ->
          let result = R.verify program in
          List.iter result.diagnostics ~f:Report.print_diagnostic;
          if result.verified then Logs.app (fun m -> m "Verification successful.");
          result.verified)
