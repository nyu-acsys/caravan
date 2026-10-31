(* The laws of the history algebra that translations emit trusted hold. *)

module R = Raven_api
module C = Caravan_core

let () =
  let program = R.Program.make ~loc:R.Loc.none C.Monotone_history.checked_members in
  let result = R.verify ~options:{ R.default_options with smt_timeout = 60000 } program in
  List.iter (fun (d : R.Diagnostic.t) -> prerr_endline d.message) result.diagnostics;
  assert result.verified
