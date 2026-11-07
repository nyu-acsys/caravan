(** Automatic views observe values through fractional agreement, including values whose
    source type is itself a resource algebra. *)

open Base
module R = Raven_api

type t = { field : string; value_type : R.Type.t }

let name ~loc text = Qualified_name.raven ~loc (Qualified_name.of_string text)

let algebra field =
  let qualified = Qualified_name.of_string field in
  Qualified_name.to_string
    { qualified with name = String.capitalize qualified.name ^ "$frac" }

let store field = field ^ "$store"

let chunk ~loc ~field value fraction =
  R.Expr.call ~loc
    (name ~loc (algebra field ^ ".frac_chunk"))
    [ value; R.Expr.real ~loc fraction ]

let own ~loc ~field cell value fraction =
  R.Expr.own ~loc
    [ R.Expr.field ~loc cell (name ~loc field); chunk ~loc ~field value fraction ]

let write ~loc ~field cell value =
  R.Stmt.call ~loc (R.Expr.call ~loc (name ~loc (store field)) [ cell; value ])

let members ~loc ~local_name { field; value_type } =
  let ident text = R.Ident.make ~loc (local_name text) in
  let variable text = R.Expr.var ~loc (R.Name.make ~loc text) in
  let formal text typ = R.Var.make ~loc (R.Ident.make ~loc text) typ in
  let cell = variable "cell" and next = variable "next" in
  let owned value = own ~loc ~field cell value 1.0 in
  let frac = name ~loc "Library.Frac" in
  [
    R.Member.instance ~loc ~def:(frac, [ value_type ]) (ident (algebra field)) frac;
    R.Member.field ~loc ~ghost:true (ident field)
      (R.Type.named ~loc (name ~loc (algebra field ^ ".T")) []);
    R.Member.callable
      (R.Callable.proc ~loc ~kind:Lemma
         ~formals:[ formal "cell" (R.Type.ref ~loc); formal "next" value_type ]
         ~requires:
           [
             R.Spec.make
               (R.Expr.exists ~loc
                  [ formal "previous" value_type ]
                  (owned (variable "previous")));
           ]
         ~ensures:[ R.Spec.make (owned next) ]
         (ident (store field))
         (Some
            [
              R.Stmt.call ~loc
                (R.Expr.call ~loc (name ~loc "fpu")
                   [
                     R.Expr.field ~loc cell (name ~loc field); chunk ~loc ~field next 1.0;
                   ]);
            ]));
  ]
