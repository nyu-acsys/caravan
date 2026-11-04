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

type result = {
  file : string;
  verified : bool;
  diagnostics : R.Diagnostic.t list;
  dependencies : string list;
  annotations : Editor_annotations.t list;
}

type prepared = {
  program : R.Program.t;
  origins : Translate_context.origin list;
  warnings : R.Diagnostic.t list;
  explicit_proof_files : string list;
  dependencies : string list;
  annotations : Editor_annotations.t list;
}

let sibling_dependencies file =
  let base = Stdlib.Filename.remove_extension file in
  [ file; base ^ ".mli"; base ^ ".proof" ]

let source_dependencies (source : Source.t) =
  sibling_dependencies source.file
  @ List.map source.libraries ~f:(fun library ->
      library.Source.library.scope.location.loc_start.pos_fname)
  @ List.map source.proof_scopes.declarations ~f:(fun entry ->
      entry.Proof_scopes.name.pid_loc.loc_start.pos_fname)
  |> List.filter ~f:(fun file -> not (String.is_empty file))
  |> List.dedup_and_sort ~compare:String.compare

let analyze ~include_dirs file =
  let ( let* ) result f = Result.bind result ~f in
  let* source = Source.load ~include_dirs file in
  let* scopes = Program_scopes.run source in
  Ok (source, scopes, Editor_annotations.collect scopes)

let prepare_scopes ~history (source, scopes, annotations) =
  let ( let* ) result f = Result.bind result ~f in
  let* program, origins, warnings =
    Translate.program_with_diagnostics ~history ~scopes source
  in
  let explicit_proof_files =
    List.filter_map source.proof_scopes.declarations ~f:(fun entry ->
        match entry.Proof_scopes.declaration with
        | Caravan_spec.Spec_ast.Proof_lemma _ ->
            Some entry.name.pid_loc.loc_start.pos_fname
        | _ when Option.is_some entry.scope.owner ->
            Some entry.name.pid_loc.loc_start.pos_fname
        | _ -> None)
  in
  Ok
    {
      program;
      origins;
      warnings;
      explicit_proof_files;
      dependencies = source_dependencies source;
      annotations;
    }

let prepare ~include_dirs ~history file =
  Result.bind (analyze ~include_dirs file) ~f:(prepare_scopes ~history)

let verify ~smt_timeout prepared =
  let result =
    R.verify ~options:{ R.default_options with smt_timeout } prepared.program
  in
  ( result.verified,
    prepared.warnings
    @ List.map result.diagnostics ~f:(fun diagnostic ->
        blame ~explicit_proof_files:prepared.explicit_proof_files
          (explain prepared.origins diagnostic)) )

(** Structured verification results shared by the command line and editors. *)
let analysis_error file error =
  {
    file;
    verified = false;
    diagnostics = [ Report.to_diagnostic error ];
    dependencies = sibling_dependencies file;
    annotations = [];
  }

let annotations_only ~include_dirs file =
  match analyze ~include_dirs file with
  | Error error -> analysis_error file error
  | Ok (source, _, annotations) ->
      {
        file;
        verified = false;
        diagnostics = [];
        dependencies = source_dependencies source;
        annotations;
      }

let run ~include_dirs ~history ~smt_timeout file =
  match analyze ~include_dirs file with
  | Error error -> analysis_error file error
  | Ok ((source, _, annotations) as analysis) ->
      begin match prepare_scopes ~history analysis with
      | Error error ->
          {
            file;
            verified = false;
            diagnostics = [ Report.to_diagnostic error ];
            dependencies = source_dependencies source;
            annotations;
          }
      | Ok prepared ->
          let verified, diagnostics = verify ~smt_timeout prepared in
          {
            file;
            verified;
            diagnostics;
            dependencies = prepared.dependencies;
            annotations = prepared.annotations;
          }
      end

(** The human-readable command line, including the generated-program escape hatch. *)
let file ~include_dirs ~history ~emit_rav ~smt_timeout file =
  if emit_rav then (
    match prepare ~include_dirs ~history file with
    | Error error ->
        Report.print error;
        false
    | Ok prepared ->
        List.iter prepared.warnings ~f:Report.print_diagnostic;
        Logs.app (fun m -> m "%a" R.Program.pr prepared.program);
        true)
  else
    let result = run ~include_dirs ~history ~smt_timeout file in
    List.iter result.diagnostics ~f:Report.print_diagnostic;
    if result.verified then Logs.app (fun m -> m "Verification successful.");
    result.verified
