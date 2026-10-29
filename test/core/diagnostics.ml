module R = Raven_api
module C = Caravan_core

let () =
  let position = { Lexing.dummy_pos with pos_fname = "queue.ml"; pos_cnum = 12 } in
  let at = { Location.loc_start = position; loc_end = position; loc_ghost = false } in
  let loc = R.Loc.make position position in
  let message = "The invariant is_queue may not hold after this step" in
  let origin : C.Translate_context.origin =
    { at; code = Fold; message; related = [ (at, "The invariant") ] }
  in
  let diagnostic : R.Diagnostic.t =
    {
      severity = Error;
      kind = Verification;
      code = Some Fold;
      loc;
      message = "Failed to fold predicate. The solver timed out (see --smt-timeout)";
      related = [];
    }
  in
  let explained = C.Check.explain [ origin ] diagnostic in
  assert (explained.message = message ^ ". The solver timed out (see --smt-timeout)");
  assert (List.length explained.related = 1);
  let origin = { origin with related = [] } in
  let explained = C.Check.explain [ origin ] diagnostic in
  assert (explained.message = message ^ ". The solver timed out (see --smt-timeout)");
  let diagnostic = { diagnostic with message = "Failed to fold predicate" } in
  assert ((C.Check.explain [ origin ] diagnostic).message = message);
  assert ((C.Check.explain [] diagnostic).message = diagnostic.message)
