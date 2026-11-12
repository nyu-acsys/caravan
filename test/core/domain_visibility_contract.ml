(** Domain handoffs suspend live authorities and consume completion resources. *)

open Base
module R = Raven_api
module E = Caravan_core.Execution_contract
module V = Caravan_core.Visibility_contract

let loc = R.Loc.none
let ident = R.Ident.make ~loc
let name = R.Name.make ~loc
let var text = R.Expr.var ~loc (name text)
let parent = var "parent"
let child = var "child"
let foreign = var "foreign"
let reference text = R.Var.make ~loc ~ghost:true (ident text) (R.Type.ref ~loc)
let call expression = R.Stmt.call ~loc expression

let owner text expression =
  R.Stmt.local ~loc ~ghost:true ~typ:(R.Type.ref ~loc) ~init:(R.Stmt.expr_rhs expression)
    (ident text)

type probe = Valid | Transfer_after_end | Finish_during_handoff | Foreign_parent

let client probe =
  let snapshot =
    R.Stmt.local ~loc ~ghost:true ~typ:(V.view_type ~loc)
      ~init:(R.Stmt.expr_rhs (V.snapshot ~loc ~module_name:E.module_name parent))
      (ident "initial_view")
  in
  let statements =
    owner "parent" (E.start ~loc)
    @ snapshot
    @ owner "child"
        (E.start_child ~loc (match probe with Foreign_parent -> foreign | _ -> parent))
    @ (match probe with
      | Finish_during_handoff -> [ call (E.finish ~loc parent) ]
      | Valid | Transfer_after_end | Foreign_parent -> [])
    @ (match probe with
      | Transfer_after_end -> []
      | Valid | Finish_during_handoff | Foreign_parent ->
          [ call (E.visibility_transfer ~loc parent child (var "initial_view")) ])
    @ [ call (E.visibility_end_handoff ~loc parent child) ]
    @ (match probe with
      | Transfer_after_end ->
          [ call (E.visibility_transfer ~loc parent child (var "initial_view")) ]
      | Valid | Finish_during_handoff | Foreign_parent -> [])
    @ [
        call (E.finish ~loc child);
        call (E.begin_join ~loc parent child);
        call (E.visibility_end_handoff ~loc child parent);
        call (E.finish ~loc child);
        call (E.finish ~loc parent);
      ]
  in
  R.Member.callable
    (R.Callable.proc ~loc
       ~formals:[ reference "foreign" ]
       (ident "client") (Some statements))

let check ~mutex probe =
  let result =
    R.verify
      (R.Program.make ~loc
         (Caravan_core.Prelude.value_signature
         :: (E.support ~loc ~mutex ~visibility:true () @ [ client probe ])))
  in
  match probe with
  | Valid ->
      if not result.verified then
        failwith
          (String.concat ~sep:"\n"
             (List.map result.diagnostics ~f:R.Diagnostic.to_string))
  | Transfer_after_end | Finish_during_handoff | Foreign_parent ->
      assert (not result.verified);
      assert (
        List.exists result.diagnostics ~f:(fun diagnostic ->
            Poly.equal diagnostic.R.Diagnostic.code (Some R.Diagnostic.Precondition)))

let () =
  List.iter [ false; true ] ~f:(fun mutex ->
      List.iter
        [ Valid; Transfer_after_end; Finish_during_handoff; Foreign_parent ]
        ~f:(check ~mutex))
