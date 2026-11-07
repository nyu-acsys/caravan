(** The monotone resource algebra that histories of states are: an authority holding the
    current state, and fragments holding lower bounds of it, composed by their join. The
    states form a [JoinOrder], an order with joins of compatible elements. *)

open Base
module R = Raven_api

(** The interface of the orders of states. *)
let order_interface = "JoinOrder"

(** The resource algebra of the histories over an order. *)
let algebra = "MonoRA"

let loc = R.Loc.none
let ident x = R.Ident.make ~loc x
let name x = R.Name.make ~loc x
let var x = R.Expr.var ~loc (name x)
let call f args = R.Expr.call ~loc f args
let bin = R.Expr.binary ~loc
let decl x t = R.Var.make ~loc (ident x) t
let a = var "a"
let b = var "b"
let c = var "c"

(* The order's type and functions, inside an order. *)
let t = R.Type.named ~loc (name "T") []
let le a b = call (name "le") [ a; b ]
let compat a b = call (name "compat") [ a; b ]
let join a b = call (name "join") [ a; b ]

let law kind ~auto law_name vars ~triggers body =
  R.Member.callable
    (R.Callable.proc ~loc ~kind ~auto
       ~ensures:
         [
           R.Spec.make
             (R.Expr.forall ~loc ~triggers (List.map vars ~f:(fun x -> decl x t)) body);
         ]
       (ident law_name)
       (match kind with Lemma -> Some [] | Proc | Axiom -> None))

(** The laws of an order, but that bounded elements are compatible, as [kind]: axioms of
    the interface, which apply automatically, or lemmas that an order's module proves,
    which apply where they are called. *)
let laws kind =
  let law = law kind ~auto:(match kind with R.Callable.Axiom -> true | _ -> false) in
  [
    law "leRefl" [ "a" ] ~triggers:[ [ le a a ] ] (le a a);
    law "leTrans" [ "a"; "b"; "c" ]
      ~triggers:[ [ le a b; le b c ] ]
      (bin Impl (bin And (le a b) (le b c)) (le a c));
    law "compatCommute" [ "a"; "b" ]
      ~triggers:[ [ compat a b ] ]
      (bin Eq (compat a b) (compat b a));
    law "joinCommute" [ "a"; "b" ]
      ~triggers:[ [ join a b ] ]
      (bin Impl (compat a b) (bin Eq (join a b) (join b a)));
    law "joinUpper" [ "a"; "b" ]
      ~triggers:[ [ join a b ] ]
      (bin Impl (compat a b) (le a (join a b)));
    law "joinAbsorb" [ "a"; "b" ]
      ~triggers:[ [ le a b ] ]
      (bin Impl (le a b) (bin And (compat a b) (bin Eq (join a b) b)));
    law "joinAssoc" [ "a"; "b"; "c" ]
      ~triggers:[ [ join (join a b) c ] ]
      (bin Impl
         (bin And (compat a b) (compat (join a b) c))
         (bin And
            (bin And (compat b c) (compat a (join b c)))
            (bin Eq (join (join a b) c) (join a (join b c)))));
  ]

(* The interface of the orders, and the algebra over them. *)
let order, ra =
  let ite = R.Expr.ite ~loc in
  let is e c = R.Expr.is_ ~loc e (ident c) in
  let field e f = R.Expr.field ~loc e (name f) in
  let bool = R.Type.bool ~loc in
  let bounded_compat =
    law R.Callable.Axiom ~auto:true "boundedCompat" [ "a"; "b"; "c" ]
      ~triggers:[ [ le a c; le b c ] ]
      (bin Impl (bin And (le a c) (le b c)) (compat a b))
  in
  let signature f formals returns =
    R.Member.callable
      (R.Callable.func ~loc ~formals ~returns:[ decl "ret" returns ] (ident f) None)
  in
  let order =
    R.Member.module_ ~loc ~interface:true
      ~implements:[ (R.Name.make ~loc ~path:[ "Library" ] "Type", []) ]
      (ident order_interface)
      ([
         R.Member.type_ ~loc ~rep:true (ident "T") None;
         signature "le" [ decl "a" t; decl "b" t ] bool;
         signature "compat" [ decl "a" t; decl "b" t ] bool;
         signature "join" [ decl "a" t; decl "b" t ] t;
       ]
      @ laws R.Callable.Axiom @ [ bounded_compat ])
  in
  (* The algebra, over the order [P]. *)
  let p x = R.Name.make ~loc ~path:[ "P" ] x in
  let pt = R.Type.named ~loc (p "T") [] in
  let ple a b = call (p "le") [ a; b ] in
  let pcompat a b = call (p "compat") [ a; b ] in
  let pjoin a b = call (p "join") [ a; b ] in
  let element = R.Type.named ~loc (name "T") [] in
  let case x = var x and make c args = call (name c) args in
  let null = case "m_null" and top = case "m_top" and none = case "m_none" in
  let frag e = make "m_frag" [ e ] and auth_frag e f = make "m_auth_frag" [ e; f ] in
  let func f formals returns body =
    R.Member.callable
      (R.Callable.func ~loc ~formals
         ~returns:[ decl "ret" returns ]
         (ident f) (Some body))
  in
  let lb e = field e "lb" and cur e = field e "cur" in
  let af_cur e = field e "af_cur" and af_lb e = field e "af_lb" in
  let or_ = bin Or and and_ = bin And and eq = bin Eq in
  (* The join of the lower bounds [x] and [y], as [m_frag] or with the authority [current]
     makes: the larger one when they are comparable. *)
  let joined x y ~larger_x ~larger_y ~joined =
    ite (ple x y) larger_y (ite (ple y x) larger_x (ite (pcompat x y) joined top))
  in
  let comp =
    ite (eq a null) b
      (ite (eq b null) a
         (ite
            (or_ (is a "m_none") (is b "m_none"))
            top
            (ite
               (and_ (is a "m_frag") (is b "m_frag"))
               (joined (lb a) (lb b) ~larger_x:a ~larger_y:b
                  ~joined:(frag (pjoin (lb a) (lb b))))
               (ite
                  (and_ (is a "m_frag") (is b "m_auth"))
                  (auth_frag (cur b) (lb a))
                  (ite
                     (and_ (is a "m_auth") (is b "m_frag"))
                     (auth_frag (cur a) (lb b))
                     (ite
                        (and_ (is a "m_frag") (is b "m_auth_frag"))
                        (joined (lb a) (af_lb b)
                           ~larger_x:(auth_frag (af_cur b) (lb a))
                           ~larger_y:b
                           ~joined:(auth_frag (af_cur b) (pjoin (lb a) (af_lb b))))
                        (ite
                           (and_ (is a "m_auth_frag") (is b "m_frag"))
                           (joined (af_lb a) (lb b) ~larger_x:a
                              ~larger_y:(auth_frag (af_cur a) (lb b))
                              ~joined:(auth_frag (af_cur a) (pjoin (af_lb a) (lb b))))
                           top)))))))
  in
  let frame =
    ite (eq b null) a
      (ite
         (and_ (is a "m_none") (is b "m_none"))
         null
         (ite
            (and_ (is a "m_frag") (is b "m_frag"))
            (ite (ple (lb b) (lb a)) a top)
            (ite
               (and_ (is a "m_auth_frag") (is b "m_frag"))
               (ite (ple (lb b) (af_lb a)) a top)
               (ite
                  (and_ (is a "m_auth") (is b "m_auth"))
                  (ite (eq (cur a) (cur b)) null top)
                  (ite
                     (and_ (is a "m_auth_frag") (is b "m_auth"))
                     (ite (eq (af_cur a) (cur b)) (frag (af_lb a)) top)
                     (ite
                        (and_ (is a "m_auth_frag") (is b "m_auth_frag"))
                        (ite
                           (and_ (eq (af_cur a) (af_cur b)) (ple (af_lb b) (af_lb a)))
                           (frag (af_lb a))
                           top)
                        top))))))
  in
  let valid e = call (name "valid") [ e ] in
  let current e = call (name "current") [ e ] in
  let fpu_allowed =
    or_ (eq a b)
      (or_
         (and_ (is a "m_none")
            (and_ (valid b) (or_ (is b "m_auth") (is b "m_auth_frag"))))
         (and_
            (and_ (or_ (is a "m_auth") (is a "m_auth_frag")) (valid a))
            (or_
               (and_ (is b "m_auth") (ple (current a) (cur b)))
               (and_
                  (and_ (is b "m_auth_frag") (ple (current a) (af_lb b)))
                  (ple (af_lb b) (af_cur b))))))
  in
  let s = var "s" and u = var "u" in
  let ra =
    R.Member.module_ ~loc
      ~params:[ (ident "P", name order_interface) ]
      ~implements:[ (R.Name.make ~loc ~path:[ "Library" ] "ResourceAlgebra", []) ]
      (ident algebra)
      [
        R.Member.type_ ~loc ~rep:true (ident "T")
          (Some
             (R.Type.data ~loc
                [
                  R.Type.variant ~loc (ident "m_null") [];
                  R.Type.variant ~loc (ident "m_none") [];
                  R.Type.variant ~loc (ident "m_frag") [ (ident "lb", pt) ];
                  R.Type.variant ~loc (ident "m_auth") [ (ident "cur", pt) ];
                  R.Type.variant ~loc (ident "m_auth_frag")
                    [ (ident "af_cur", pt); (ident "af_lb", pt) ];
                  R.Type.variant ~loc (ident "m_top") [];
                ]));
        R.Member.value ~loc ~typ:element (ident "id") (Some null);
        func "valid"
          [ decl "n" element ]
          bool
          (ite
             (is (var "n") "m_auth_frag")
             (ple (af_lb (var "n")) (af_cur (var "n")))
             (R.Expr.not_ ~loc (is (var "n") "m_top")));
        func "comp" [ decl "a" element; decl "b" element ] element comp;
        func "frame" [ decl "a" element; decl "b" element ] element frame;
        func "current" [ decl "a" element ] pt (ite (is a "m_auth") (cur a) (af_cur a));
        func "fpuAllowed" [ decl "a" element; decl "b" element ] bool fpu_allowed;
        func "empty" [] element none;
        func "frag" [ decl "s" pt ] element (frag s);
        func "auth" [ decl "s" pt ] element (make "m_auth" [ s ]);
        func "auth_frag" [ decl "s" pt; decl "u" pt ] element (auth_frag s u);
        func "full" [ decl "s" pt ] element (auth_frag s s);
      ]
  in
  (order, ra)

(** The interface of the orders, and the algebra over them, whose laws Raven checks. *)
let checked_members = [ order; ra ]

(** The interface of the orders, and the algebra over them, trusted as Raven's own
    algebras are: its laws hold of every order, as a test checks with {!checked_members}.
*)
let members = [ order; R.Member.free ra ]
