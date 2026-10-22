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
  let origin =
    List.find origins ~f:(fun o ->
        same_place o.at d.loc && Option.exists d.code ~f:(Poly.equal o.code))
  in
  match origin with
  | Some { message; related = []; _ } -> { d with message }
  | Some { message; related; _ } ->
      {
        d with
        message;
        related =
          List.map related ~f:(fun (at, related_message) ->
              { R.Diagnostic.related_loc = Report.loc at; related_message });
      }
  | None -> d

(** [d], an error of Raven on the generated program, reported as the bug in Caravan it is
    if it is not about the user's code: a type or syntax error, or one outside the user's
    files. *)
let blame (d : R.Diagnostic.t) : R.Diagnostic.t =
  let user_file =
    let file = (R.Loc.start d.loc).pos_fname in
    List.exists [ ".ml"; ".mli"; ".proof" ] ~f:(fun suffix ->
        String.is_suffix file ~suffix)
  in
  let generated =
    match d.kind with Type | Syntax | Internal -> true | _ -> not user_file
  in
  match d.severity with
  | Error when generated ->
      {
        d with
        kind = Internal;
        message =
          "Caravan generated Raven that Raven rejects, a bug in Caravan; Raven says: "
          ^ d.message;
      }
  | _ -> d

(** Verifies [file], giving the solver [smt_timeout] milliseconds a query; whether it
    verified. With [emit_rav], the Raven program is printed instead. *)
let file ~(emit_rav : bool) ~(smt_timeout : int) (file : string) : bool =
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
          let result = R.verify ~options:{ R.default_options with smt_timeout } program in
          List.iter result.diagnostics ~f:(fun d ->
              Report.print_diagnostic (blame (explain origins d)));
          if result.verified then Logs.app (fun m -> m "Verification successful.");
          result.verified)
