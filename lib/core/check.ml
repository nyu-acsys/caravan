(** Verifying OCaml files: reading, translating, and verifying with Raven. *)

open Base
module R = Raven_api

let same_place (at : Location.t) (l : R.Loc.t) =
  let same (p : Lexing.position) (q : Lexing.position) =
    String.equal p.pos_fname q.pos_fname && p.pos_cnum = q.pos_cnum
  in
  same at.loc_start (R.Loc.start l) && same at.loc_end (R.Loc.stop l)

(** [d], saying what failed if it is the failure of a check the translation generated. *)
let explain (origins : Translate_context.origin list) (d : R.Diagnostic.t) :
    R.Diagnostic.t =
  let explain_message message =
    let timeout = ". The solver timed out (see --smt-timeout)" in
    if String.is_suffix d.message ~suffix:timeout then message ^ timeout else message
  in
  let origin =
    List.find origins ~f:(fun o ->
        same_place o.at d.loc && Option.exists d.code ~f:(Poly.equal o.code))
  in
  match origin with
  | Some { message; related = []; _ } -> { d with message = explain_message message }
  | Some { message; related; _ } ->
      {
        d with
        message = explain_message message;
        related =
          List.map related ~f:(fun (at, related_message) ->
              { R.Diagnostic.related_loc = Report.loc at; related_message });
      }
  | None -> d

(** Type errors in explicit proof files belong to the user; errors in generated syntax,
    runtime types, or constructs outside the user's files belong to Caravan. *)
let blame ~explicit_proof_files (d : R.Diagnostic.t) : R.Diagnostic.t =
  let user_file =
    let file = (R.Loc.start d.loc).pos_fname in
    List.exists [ ".ml"; ".mli"; ".proof" ] ~f:(fun suffix ->
        String.is_suffix file ~suffix)
  in
  let explicit_proof =
    List.mem explicit_proof_files (R.Loc.start d.loc).pos_fname ~equal:String.equal
  in
  let generated =
    match d.kind with
    | Type when explicit_proof -> false
    | Type | Syntax | Internal -> true
    | _ -> not user_file
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

(** Verifies [file], with the libraries in [include_dirs], encoding histories in [history]
    and giving the solver [smt_timeout] milliseconds a query; whether it verified. With
    [emit_rav], the Raven program is printed instead. *)
let file ~(include_dirs : string list) ~(history : History.encoding) ~(emit_rav : bool)
    ~(smt_timeout : int) (file : string) : bool =
  match Source.load ~include_dirs file with
  | Error error ->
      Report.print error;
      false
  | Ok source -> (
      match Translate.program ~history source with
      | Error error ->
          Report.print error;
          false
      | Ok (program, _) when emit_rav ->
          Logs.app (fun m -> m "%a" R.Program.pr program);
          true
      | Ok (program, origins) ->
          let result = R.verify ~options:{ R.default_options with smt_timeout } program in
          let explicit_proof_files =
            List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
                match entry.Proof_scopes.declaration with
                | Caravan_spec.Spec_ast.Proof_lemma _ ->
                    Some entry.name.pid_loc.loc_start.pos_fname
                | _ when Option.is_some entry.scope.owner ->
                    Some entry.name.pid_loc.loc_start.pos_fname
                | _ -> None)
          in
          List.iter result.diagnostics ~f:(fun d ->
              Report.print_diagnostic (blame ~explicit_proof_files (explain origins d)));
          if result.verified then Logs.app (fun m -> m "Verification successful.");
          result.verified)
