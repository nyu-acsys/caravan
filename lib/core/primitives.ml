(** The atomic read-modify-write operations of [Atomic], as Raven procedures on the field
    of the atomics with contents of one type, declared physically atomic.

    [compare_and_set] compares physically. On values that are not immediate, physical
    equality implies equality but not conversely, so on these it may fail even if the
    values are equal. *)

open Base
module R = Raven_api

type op = Compare_and_set | Exchange | Fetch_and_add

let op_name = function
  | Compare_and_set -> "compare_and_set"
  | Exchange -> "exchange"
  | Fetch_and_add -> "fetch_and_add"

(** The procedure performing [op] on [field]. *)
let name ~field op = field ^ "_" ^ op_name op

let loc = R.Loc.none
let var x = R.Expr.var ~loc (R.Name.make ~loc x)
let ident x = R.Ident.make ~loc x
let bin op a b = R.Expr.binary ~loc op a b
let call f args = R.Expr.call ~loc (R.Name.make ~loc f) args
let assign xs v = R.Stmt.assign ~loc (List.map xs ~f:var) (R.Stmt.expr_rhs v)

type ordinary_op = Read | Write

let ordinary_name ~field = function
  | Read -> field ^ "_ordinary_read"
  | Write -> field ^ "_ordinary_write"

(** An ordinary field access is a call so it cannot be used as an atomic step. *)
let ordinary_proc ?declaration_name ~field ~(typ : R.Type.t) ~int op : R.Member.t =
  let x = var "x" and v = var "v" in
  let content =
    R.Expr.field ~loc x (Qualified_name.raven ~loc (Qualified_name.of_string field))
  in
  let formal x t = R.Var.make ~loc (ident x) t in
  let ghost x t = R.Var.make ~loc ~ghost:true ~implicit:true (ident x) t in
  let one = R.Expr.real ~loc 1.0 in
  let own value fraction = R.Expr.own ~loc [ content; value; fraction ] in
  let formals, returns, requires, ensures, body =
    match op with
    | Read ->
        (* Separate clauses keep ownership transfers adjacent for fusion. *)
        let q = var "q" in
        ( [ formal "x" (R.Type.ref ~loc); ghost "v" typ; ghost "q" (R.Type.real ~loc) ],
          [ formal "r" typ ],
          [ R.Spec.make (bin Gt q (R.Expr.real ~loc 0.0)); R.Spec.make (own v q) ],
          [ R.Spec.make (own v q); R.Spec.make (bin Eq (var "r") v) ],
          [ assign [ "r" ] content ] )
    | Write ->
        let new_val = var "new_val" in
        ( [ formal "x" (R.Type.ref ~loc); formal "new_val" typ; ghost "v" typ ],
          [],
          (if int then [ R.Spec.make (call Prelude.in_range [ new_val ]) ] else [])
          @ [ R.Spec.make (own v one) ],
          [ R.Spec.make (own new_val one) ],
          [ R.Stmt.assign ~loc [ content ] (R.Stmt.expr_rhs new_val) ] )
  in
  R.Member.callable
    (R.Callable.proc ~loc ~formals ~returns ~requires ~ensures
       (ident (Option.value declaration_name ~default:(ordinary_name ~field op)))
       (Some body))

(** The procedure performing [op] on [field], whose values have type [typ]; [exact] if
    they are immediate, [int] if they are OCaml's [int]s, which the values written are
    then required to be. *)
let proc ~field ~(typ : R.Type.t) ~exact ~int op : R.Member.t =
  let x = var "x" and v = var "v" and q = var "q" in
  let content =
    R.Expr.field ~loc x (Qualified_name.raven ~loc (Qualified_name.of_string field))
  in
  let own value = R.Expr.own ~loc [ content; value; q ] in
  let formal x t = R.Var.make ~loc (ident x) t in
  let ghost x t = R.Var.make ~loc ~ghost:true ~implicit:true (ident x) t in
  let bool = R.Type.bool ~loc and real = R.Type.real ~loc in
  let one = R.Expr.real ~loc 1.0 in
  let full = bin Eq q one in
  let args, ret, pre, post, update =
    match op with
    | Compare_and_set ->
        let old_val = var "old_val" and new_val = var "new_val" in
        let same = bin Eq v old_val in
        let changed = if exact then same else var "b" in
        ( [ formal "old_val" typ; formal "new_val" typ ],
          formal "b" bool,
          (* A write needs the whole location, a read a fraction of it. *)
          R.Expr.ite ~loc same full (bin Gt q (R.Expr.real ~loc 0.0)),
          bin And
            (own (R.Expr.ite ~loc changed new_val v))
            (if exact then bin Eq (var "b") same else bin Impl (var "b") same),
          let cur = var "cur" in
          let test =
            if exact then bin Eq cur old_val
            else bin And (bin Eq cur old_val) (var "same")
          in
          R.Stmt.local ~loc ~const:true ~typ ~init:(R.Stmt.expr_rhs content) (ident "cur")
          @ (if exact then []
             else
               R.Stmt.local ~loc ~typ:bool (ident "same")
               @ [ R.Stmt.havoc ~loc (R.Name.make ~loc "same") ])
          @ [
              R.Stmt.if_ ~loc test
                [
                  R.Stmt.assign ~loc [ content ] (R.Stmt.expr_rhs new_val);
                  assign [ "b" ] (R.Expr.bool ~loc true);
                ]
                [ assign [ "b" ] (R.Expr.bool ~loc false) ];
            ] )
    | Exchange ->
        ( [ formal "new_val" typ ],
          formal "r" typ,
          full,
          bin And (own (var "new_val")) (bin Eq (var "r") v),
          [
            assign [ "r" ] content;
            R.Stmt.assign ~loc [ content ] (R.Stmt.expr_rhs (var "new_val"));
          ] )
    | Fetch_and_add ->
        (* OCaml's integers wrap around. *)
        let sum = call Prelude.wrap [ bin Plus v (var "n") ] in
        ( [ formal "n" typ ],
          formal "r" typ,
          full,
          bin And (own sum) (bin Eq (var "r") v),
          [
            assign [ "r" ] content;
            R.Stmt.assign ~loc [ content ]
              (R.Stmt.expr_rhs (call Prelude.wrap [ bin Plus (var "r") (var "n") ]));
          ] )
  in
  R.Member.callable
    (R.Callable.proc ~loc ~atomic:true
       ~formals:
         ((formal "x" (R.Type.ref ~loc) :: args) @ [ ghost "v" typ; ghost "q" real ])
       ~returns:[ ret ]
       ~requires:
         ((if int then
             let written = match op with Fetch_and_add -> "n" | _ -> "new_val" in
             [ R.Spec.make (call Prelude.in_range [ var written ]) ]
           else [])
         @ [ R.Spec.make (bin And (own v) pre) ])
       ~ensures:[ R.Spec.make post ]
       (ident (name ~field op))
       (Some update))
