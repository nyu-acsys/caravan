(** The Raven definitions every generated program includes: the range of OCaml's [int],
    its division, which rounds towards zero, in terms of Raven's, which is Euclidean, and
    its wrap-around. *)

open Base
module R = Raven_api

let loc = R.Loc.none
let div = "ocaml_div"
let mod_ = "ocaml_mod"
let in_range = "ocaml_int"
let wrap = "ocaml_wrap"
let value_interface = "Ocaml$Value"
let cell_family = "Ocaml$Cells"
let value_int = "Ocaml$IntValue"
let value_list = "Ocaml$ListValue"
let value_option = "Ocaml$OptionValue"
let value_tuple arity = "Ocaml$TupleValue$" ^ Int.to_string arity

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

let cell_members =
  let value name = R.Name.make ~loc ~path:[ "V" ] name in
  let carrier = R.Type.named ~loc (value "Carrier") [] in
  let field name =
    R.Member.field ~loc ~where:(value "holds") (R.Ident.make ~loc name) carrier
  in
  [
    R.Member.module_ ~loc
      ~params:[ (R.Ident.make ~loc "V", R.Name.make ~loc value_interface) ]
      (R.Ident.make ~loc cell_family)
      [ field "ref_contents"; field "atomic" ];
  ]

let value_signature =
  let carrier = R.Type.named ~loc (R.Name.make ~loc "Carrier") [] in
  let result = R.Expr.var ~loc (R.Name.make ~loc "result") in
  R.Member.module_ ~loc ~interface:true
    (R.Ident.make ~loc value_interface)
    [
      R.Member.type_ ~loc ~rep:true (R.Ident.make ~loc "Carrier") None;
      R.Member.callable
        (R.Callable.func ~loc
           ~returns:[ R.Var.make ~loc (R.Ident.make ~loc "result") (R.Type.bool ~loc) ]
           (R.Ident.make ~loc "unrestricted")
           None);
      R.Member.callable
        (R.Callable.func ~loc
           ~formals:[ R.Var.make ~loc (R.Ident.make ~loc "value") carrier ]
           ~returns:[ R.Var.make ~loc (R.Ident.make ~loc "result") (R.Type.bool ~loc) ]
           ~ensures:
             [
               R.Spec.make
                 (R.Expr.binary ~loc Impl
                    (R.Expr.call ~loc (R.Name.make ~loc "unrestricted") [])
                    result);
             ]
           (R.Ident.make ~loc "holds") None);
    ]

(** A value dictionary shares the total holds contract across leaf and container
    implementations. The carrier alias does not require an automatic Type provider. *)
let value_dictionary_with_members ~loc ~parameters ~name ~carrier ~unrestricted ~body
    ~members =
  let ident text = R.Ident.make ~loc text in
  let variable text = R.Expr.var ~loc (R.Name.make ~loc text) in
  let own_carrier = R.Type.named ~loc (R.Name.make ~loc "Carrier") [] in
  R.Member.module_ ~loc ~params:parameters
    ~implements:[ (R.Name.make ~loc value_interface, []) ]
    (ident name)
    ((R.Member.type_ ~loc ~rep:true (ident "Carrier") (Some carrier) :: members)
    @ [
        R.Member.callable
          (R.Callable.func ~loc
             ~returns:[ R.Var.make ~loc (ident "result") (R.Type.bool ~loc) ]
             (ident "unrestricted") (Some unrestricted));
        R.Member.callable
          (R.Callable.func ~loc
             ~formals:[ R.Var.make ~loc (ident "value") own_carrier ]
             ~returns:[ R.Var.make ~loc (ident "result") (R.Type.bool ~loc) ]
             ~ensures:
               [
                 R.Spec.make
                   (R.Expr.binary ~loc Impl
                      (R.Expr.call ~loc (R.Name.make ~loc "unrestricted") [])
                      (variable "result"));
               ]
             (ident "holds") (Some body));
      ])

let value_dictionary_parameters ~loc ~parameters ~name ~carrier ~unrestricted ~body =
  value_dictionary_with_members ~loc ~parameters ~name ~carrier ~unrestricted ~body
    ~members:[]

let value_dictionary ~loc ~name ~carrier ~unrestricted ~body =
  value_dictionary_parameters ~loc ~parameters:[] ~name ~carrier ~unrestricted ~body

(** Canonical container dictionaries alias existing carriers. Their unrestricted flag
    permits trivial element domains to avoid recursive container reasoning. *)
let value_functors ?(integers = true) ?(lists = true) ?(options = true) ~tuple_arities ()
    =
  let ident name = R.Ident.make ~loc name in
  let name text = R.Name.make ~loc text in
  let member path field = R.Name.make ~loc ~path field in
  let call path field args = R.Expr.call ~loc (member path field) args in
  let named path field = R.Type.named ~loc (member path field) [] in
  let value = var "value" in
  let conjunction expressions =
    Option.value
      (List.reduce expressions ~f:(R.Expr.binary ~loc And))
      ~default:(R.Expr.bool ~loc true)
  in
  let dictionary ~parameters name carrier unrestricted body =
    value_dictionary_parameters ~loc ~parameters ~name ~carrier ~unrestricted ~body
  in
  let parameter name_ = (ident name_, name value_interface) in
  let element_carrier = named [ "E" ] "Carrier" in
  let element_unrestricted = call [ "E" ] "unrestricted" [] in
  let own_unrestricted = call [] "unrestricted" [] in
  let structural body = R.Expr.ite ~loc own_unrestricted (R.Expr.bool ~loc true) body in
  let integer_member =
    dictionary ~parameters:[] value_int (R.Type.int ~loc) (R.Expr.bool ~loc false)
      (R.Expr.call ~loc (name in_range) [ value ])
  in
  let list_member =
    let head = var "item$head" and tail = var "item$tail" in
    let body =
      R.Expr.match_ ~loc value
        [
          (R.Expr.Case (ident "nil", []), R.Expr.bool ~loc true);
          ( R.Expr.Case (ident "::", [ ident "item$head"; ident "item$tail" ]),
            conjunction [ call [ "E" ] "holds" [ head ]; call [] "holds" [ tail ] ] );
        ]
    in
    dictionary
      ~parameters:[ parameter "E" ]
      value_list
      (R.Type.named ~loc (member [ "Library" ] "List") [ element_carrier ])
      element_unrestricted (structural body)
  in
  let option_member =
    let item = var "item$value" in
    let body =
      R.Expr.match_ ~loc value
        [
          (R.Expr.Case (ident "none", []), R.Expr.bool ~loc true);
          ( R.Expr.Case (ident "some", [ ident "item$value" ]),
            call [ "E" ] "holds" [ item ] );
        ]
    in
    dictionary
      ~parameters:[ parameter "E" ]
      value_option
      (R.Type.named ~loc (member [ "Library" ] "Option") [ element_carrier ])
      element_unrestricted (structural body)
  in
  let tuple arity =
    let parameters = List.init arity ~f:(fun i -> "E" ^ Int.to_string i) in
    let carrier =
      R.Type.tuple ~loc (List.map parameters ~f:(fun p -> named [ p ] "Carrier"))
    in
    let unrestricted =
      conjunction (List.map parameters ~f:(fun p -> call [ p ] "unrestricted" []))
    in
    let body =
      conjunction
        (List.mapi parameters ~f:(fun i p ->
             let item = if arity = 1 then value else R.Expr.tuple_get ~loc value i in
             call [ p ] "holds" [ item ]))
    in
    dictionary
      ~parameters:(List.map parameters ~f:parameter)
      (value_tuple arity) carrier unrestricted (structural body)
  in
  List.filter_map
    [ (integers, integer_member); (lists, list_member); (options, option_member) ]
    ~f:(fun (needed, member) -> Option.some_if needed member)
  @ List.map (List.dedup_and_sort tuple_arities ~compare:Int.compare) ~f:tuple

(** The canonical carrier value used where an exception leaves no runtime result. *)
let unspecified_value ~loc typ =
  R.Expr.annotated
    (R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Ocaml$Unspecified" ] "value") [])
    typ

let unspecified_member =
  let carrier = R.Type.named ~loc (R.Name.make ~loc "E") [] in
  R.Member.module_ ~loc
    ~params:[ (R.Ident.make ~loc "E", R.Name.make ~loc ~path:[ "Library" ] "Type") ]
    (R.Ident.make ~loc "Ocaml$Unspecified")
    [
      R.Member.callable
        (R.Callable.func ~loc ~inline:true
           ~returns:[ R.Var.make ~loc (R.Ident.make ~loc "result") carrier ]
           (R.Ident.make ~loc "value")
           (Some (R.Expr.var ~loc (R.Name.make ~loc ~path:[ "E" ] "default"))));
    ]

let members : R.Member.t list =
  let a = var "a" and b = var "b" in
  let ocaml_div x y = R.Expr.call ~loc (R.Name.make ~loc div) [ x; y ] in
  let x = var "x" in
  let bound op n = R.Expr.binary ~loc op x (R.Expr.int ~loc n) in
  [
    value_signature;
    unspecified_member;
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
