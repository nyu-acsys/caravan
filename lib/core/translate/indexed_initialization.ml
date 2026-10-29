(** A checked inverse for a sequence of distinct allocated cells. *)

module R = Raven_api

let name = "caravan$sequence_inverse"
let call ~loc cells = R.Expr.call ~loc (R.Name.make ~loc name) [ cells ]

let members =
  let loc = R.Loc.none in
  let ident x = R.Ident.make ~loc x in
  let var x = R.Expr.var ~loc (R.Name.make ~loc x) in
  let int = R.Type.int ~loc in
  let int_var x = R.Var.make ~loc (ident x) int in
  let number = R.Expr.int ~loc in
  let bin = R.Expr.binary ~loc in
  let cells = var "cells" and index = var "index" and position = var "position" in
  let length =
    R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Library"; "Seq" ] "length") [ cells ]
  in
  let cell = R.Expr.index ~loc cells in
  let bounded i limit = bin And (bin Leq (number 0) i) (bin Lt i limit) in
  let i = var "i" and j = var "j" in
  let distinct =
    R.Expr.forall ~loc
      ~triggers:[ [ cell i; cell j ] ]
      [ int_var "i"; int_var "j" ]
      (bin Impl
         (bin And (bounded i length) (bin And (bounded j length) (bin Neq i j)))
         (bin Neq (cell i) (cell j)))
  in
  let inverse map limit =
    R.Expr.forall ~loc
      ~triggers:[ [ cell i ] ]
      [ int_var "i" ]
      (bin Impl (bounded i limit) (bin Eq (R.Expr.index ~loc map (cell i)) i))
  in
  let seq_type =
    R.Type.named ~loc (R.Name.make ~loc ~path:[ "Library" ] "Seq") [ R.Type.ref ~loc ]
  in
  let map_type = R.Type.map ~loc (R.Type.ref ~loc) int in
  let cells_var = R.Var.make ~loc (ident "cells") seq_type in
  let index_var = R.Var.make ~loc (ident "index") map_type in
  let prefix_name = name ^ "$prefix" in
  let prefix args = R.Expr.call ~loc (R.Name.make ~loc prefix_name) args in
  let current = var "current" in
  let assign value = R.Stmt.assign ~loc [ index ] (R.Stmt.expr_rhs value) in
  [
    R.Member.callable
      (R.Callable.proc ~loc ~kind:Lemma
         ~formals:
           [ cells_var; int_var "position"; R.Var.make ~loc (ident "current") map_type ]
         ~returns:[ index_var ]
         ~requires:
           [
             R.Spec.make (bin And (bin Leq (number 0) position) (bin Leq position length));
             R.Spec.make distinct;
             R.Spec.make (inverse current position);
           ]
         ~ensures:[ R.Spec.make (inverse index length) ]
         ~decreases:[ bin Minus length position ]
         (ident prefix_name)
         (Some
            [
              R.Stmt.if_ ~loc (bin Lt position length)
                [
                  assign
                    (prefix
                       [
                         cells;
                         bin Plus position (number 1);
                         R.Expr.update ~loc current (cell position) position;
                       ]);
                ]
                [ assign current ];
            ]));
    R.Member.callable
      (R.Callable.proc ~loc ~kind:Lemma ~formals:[ cells_var ] ~returns:[ index_var ]
         ~requires:[ R.Spec.make distinct ]
         ~ensures:[ R.Spec.make (inverse index length) ]
         (ident name)
         (Some
            [ assign (prefix [ cells; number 0; R.Expr.map_literal ~loc [] (number 0) ]) ]));
  ]
