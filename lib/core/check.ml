(** Verifying OCaml files: reading, translating, and verifying with Raven. *)

open Base
module R = Raven_api

let same_place (at : Location.t) (l : R.Loc.t) =
  let same (p : Lexing.position) (q : Lexing.position) =
    String.equal p.pos_fname q.pos_fname && p.pos_cnum = q.pos_cnum
  in
  same at.loc_start (R.Loc.start l) && same at.loc_end (R.Loc.stop l)

(** [d], saying what failed if it is the failure of a check the translation generated. *)
let explain (origins : Translate.origin list) (d : R.Diagnostic.t) : R.Diagnostic.t =
  match d.code with
  | Some Assertion -> (
      match List.find origins ~f:(fun o -> same_place o.at d.loc) with
      | Some o -> { d with message = o.message }
      | None -> d)
  | _ -> d

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
      | Ok (program, _) when emit_rav ->
          Logs.app (fun m -> m "%s" (R.Program.to_string program));
          true
      | Ok (program, origins) ->
          let result = R.verify program in
          List.iter result.diagnostics ~f:(fun d ->
              Report.print_diagnostic (explain origins d));
          if result.verified then Logs.app (fun m -> m "Verification successful.");
          result.verified)
