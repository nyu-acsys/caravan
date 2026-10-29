(** The Raven definitions every generated program includes: the range of OCaml's [int],
    its division, which rounds towards zero, in terms of Raven's, which is Euclidean, and
    its wrap-around. *)

module R = Raven_api

let loc = R.Loc.none
let div = "ocaml_div"
let mod_ = "ocaml_mod"
let in_range = "ocaml_int"
let wrap = "ocaml_wrap"

(** The bounds of OCaml's 63-bit [int]. *)
let min_int = Stdlib.min_int

let max_int = Stdlib.max_int
let var x = R.Expr.var ~loc (R.Name.make ~loc x)
let int_var x = R.Var.make ~loc (R.Ident.make ~loc x) (R.Type.int ~loc)

let func name ret body =
  R.Callable.func ~loc ~inline:true
    ~formals:[ int_var "a"; int_var "b" ]
    ~returns:[ int_var ret ]
    (R.Ident.make ~loc name) (Some body)

let members : R.Member.t list =
  let a = var "a" and b = var "b" in
  let ocaml_div x y = R.Expr.call ~loc (R.Name.make ~loc div) [ x; y ] in
  let x = var "x" in
  let bound op n = R.Expr.binary ~loc op x (R.Expr.int ~loc n) in
  [
    R.Member.callable
      (R.Callable.func ~loc ~inline:true
         ~formals:[ int_var "x" ]
         ~returns:[ R.Var.make ~loc (R.Ident.make ~loc "b") (R.Type.bool ~loc) ]
         (R.Ident.make ~loc in_range)
         (Some (R.Expr.binary ~loc And (bound Geq min_int) (bound Leq max_int))));
    (* The value congruent to [x] modulo 2^63 in the range, for [x] a sum of two values in
       it. *)
    R.Member.callable
      (R.Callable.func ~loc ~inline:true
         ~formals:[ int_var "x" ]
         ~returns:[ int_var "w" ]
         (R.Ident.make ~loc wrap)
         (Some
            (let n i = R.Expr.int ~loc i in
             let size =
               R.Expr.binary ~loc Plus
                 (R.Expr.binary ~loc Minus (n max_int) (n min_int))
                 (n 1)
             in
             R.Expr.ite ~loc
               (R.Expr.binary ~loc Gt x (n max_int))
               (R.Expr.binary ~loc Minus x size)
               (R.Expr.ite ~loc
                  (R.Expr.binary ~loc Lt x (n min_int))
                  (R.Expr.binary ~loc Plus x size)
                  x))));
    (* For a dividend that is not negative, Euclidean division truncates. *)
    R.Member.callable
      (func div "q"
         (R.Expr.ite ~loc
            (R.Expr.binary ~loc Geq a (R.Expr.int ~loc 0))
            (R.Expr.binary ~loc Div a b)
            (R.Expr.neg ~loc (R.Expr.binary ~loc Div (R.Expr.neg ~loc a) b))));
    R.Member.callable
      (func mod_ "r"
         (R.Expr.binary ~loc Minus a (R.Expr.binary ~loc Mult b (ocaml_div a b))));
  ]
