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
let wrap_full = "ocaml_wrap_full"
let value_interface = "Ocaml$Value"
let cell_family = "Ocaml$Cells"
let value_int = "Ocaml$IntValue"
let value_list = "Ocaml$ListValue"
let value_option = "Ocaml$OptionValue"
let value_tuple arity = "Ocaml$TupleValue$" ^ Int.to_string arity
let array_length = "array_length"
let array_entries = "array_entries"
let array_entry = "array_entry"
let array_make = "array_make"
let array_read = "array_read"
let array_write = "array_write"
let array_carrier = "Array$Carrier"
let array_entry_ra = "Array$Entry"
let array_entries_ra = "Array$Entries"

(** OCaml's [Sys.max_array_length] on 64-bit platforms. *)
let max_array_length = (1 lsl 54) - 1

(** The bounds of OCaml's machine [int]. *)
let min_int = Stdlib.min_int

let max_int = Stdlib.max_int
let var x = R.Expr.var ~loc (R.Name.make ~loc x)
let int_var x = R.Var.make ~loc (R.Ident.make ~loc x) (R.Type.int ~loc)

let func name ret body =
  R.Callable.func ~loc ~inline:true
    ~formals:[ int_var "a"; int_var "b" ]
    ~returns:[ int_var ret ]
    (R.Ident.make ~loc name) (Some body)

(** Source arithmetic normalizes every intermediate result; specifications stay
    mathematical. *)
let runtime_binary ~loc op a b =
  let call name args = R.Expr.call ~loc (R.Name.make ~loc name) args in
  match op with
  | R.Expr.Plus | Minus -> call wrap [ R.Expr.binary ~loc op a b ]
  | Mult -> call wrap_full [ R.Expr.binary ~loc op a b ]
  | Div -> call wrap [ call div [ a; b ] ]
  | Mod -> call mod_ [ a; b ]
  | _ -> R.Expr.binary ~loc op a b

let runtime_neg ~loc value =
  R.Expr.call ~loc (R.Name.make ~loc wrap) [ R.Expr.neg ~loc value ]

(** The arrays with entries of the family's carrier: an array is a single location, whose
    entries form a map of fractional values by index, so that the entries of distinct
    arrays are separate locations and a range of entries is one resource. Its length is
    fixed. *)
let array_members =
  let value name = R.Name.make ~loc ~path:[ "V" ] name in
  let carrier = R.Type.named ~loc (value "Carrier") [] in
  let local x = R.Name.make ~loc x in
  let qualified path x = R.Name.make ~loc ~path x in
  let call f args = R.Expr.call ~loc (local f) args in
  let entry f args = R.Expr.call ~loc (qualified [ array_entry_ra ] f) args in
  let typed x typ = R.Var.make ~loc (R.Ident.make ~loc x) typ in
  let ghost x typ =
    R.Var.make ~loc ~ghost:true ~implicit:true (R.Ident.make ~loc x) typ
  in
  let ref_ = R.Type.ref ~loc and int = R.Type.int ~loc and real = R.Type.real ~loc in
  let bool = R.Type.bool ~loc in
  let entry_t = R.Type.named ~loc (qualified [ array_entry_ra ] "T") [] in
  let entries_t = R.Type.named ~loc (qualified [ array_entries_ra ] "T") [] in
  let own_t = R.Type.named ~loc (local "T") [] in
  let free member = R.Member.free (R.Member.callable member) in
  let func ?body ?(inline = false) name formals ret typ =
    R.Member.callable
      (R.Callable.func ~loc ~inline ~formals
         ~returns:[ typed ret typ ]
         (R.Ident.make ~loc name) body)
  in
  let axiom name body =
    free
      (R.Callable.proc ~loc ~kind:Axiom ~auto:true
         ~ensures:[ R.Spec.make body ]
         (R.Ident.make ~loc name) None)
  in
  let proc name formals returns requires ensures =
    free
      (R.Callable.proc ~loc ~formals ~returns
         ~requires:(List.map requires ~f:R.Spec.make)
         ~ensures:(List.map ensures ~f:R.Spec.make)
         (R.Ident.make ~loc name) None)
  in
  let a = var "a" and i = var "i" and n = var "n" and k = var "k" in
  let ( &&& ) p q = R.Expr.binary ~loc And p q in
  let ( <== ) p q = R.Expr.binary ~loc Leq p q in
  let ( <<< ) p q = R.Expr.binary ~loc Lt p q in
  let ( === ) p q = R.Expr.binary ~loc Eq p q in
  let zero = R.Expr.int ~loc 0 in
  let one = R.Expr.real ~loc 1.0 in
  let key = typed "k" int in
  let at m = R.Expr.index ~loc m k in
  let pointwise f x y = R.Expr.compr ~loc key (entry f [ at x; at y ]) in
  let chunk v q = entry "frac_chunk" [ v; q ] in
  let none = R.Expr.var ~loc (qualified [ array_entry_ra ] "id") in
  let entries = R.Expr.field ~loc a (local array_entries) in
  let own_entries m = R.Expr.own ~loc [ entries; m ] in
  let x = var "x" and y = var "y" and m = var "m" in
  let carrier_type =
    R.Member.module_ ~loc
      ~implements:[ (R.Name.make ~loc ~path:[ "Library" ] "Type", []) ]
      (R.Ident.make ~loc array_carrier)
      [ R.Member.type_ ~loc ~rep:true (R.Ident.make ~loc "T") (Some carrier) ]
  in
  let entry_ra =
    R.Member.instance ~loc
      ~def:
        ( R.Name.make ~loc ~path:[ "Library" ] "Frac",
          [ R.Type.named ~loc (local array_carrier) [] ] )
      (R.Ident.make ~loc array_entry_ra)
      (R.Name.make ~loc ~path:[ "Library" ] "CancellativeResourceAlgebra")
  in
  let entries_ra =
    R.Member.module_ ~loc
      ~implements:[ (R.Name.make ~loc ~path:[ "Library" ] "ResourceAlgebra", []) ]
      (R.Ident.make ~loc array_entries_ra)
      [
        R.Member.type_ ~loc ~rep:true (R.Ident.make ~loc "T")
          (Some (R.Type.map ~loc int entry_t));
        R.Member.value ~loc ~typ:own_t (R.Ident.make ~loc "id")
          (Some (R.Expr.compr ~loc key none));
        (* Each entry is valid and holds a value of the carrier. *)
        func "valid"
          [ typed "m" own_t ]
          "ret" bool
          ~body:
            (R.Expr.forall ~loc
               ~triggers:[ [ at m ] ]
               [ key ]
               (entry "valid" [ at m ]
               &&& R.Expr.binary ~loc Impl
                     (R.Expr.is_ ~loc (at m) (R.Ident.make ~loc "frac_chunk"))
                     (R.Expr.call ~loc (value "holds")
                        [ R.Expr.field ~loc (at m) (local "frac_proj1") ])));
        func "comp"
          [ typed "x" own_t; typed "y" own_t ]
          "ret" own_t ~body:(pointwise "comp" x y);
        func "frame"
          [ typed "x" own_t; typed "y" own_t ]
          "ret" own_t ~body:(pointwise "frame" x y);
        func "fpuAllowed"
          [ typed "x" own_t; typed "y" own_t ]
          "ret" bool
          ~body:
            (call "valid" [ y ]
            &&& R.Expr.forall ~loc
                  ~triggers:[ [ at x ]; [ at y ] ]
                  [ key ]
                  (R.Expr.binary ~loc Or
                     (entry "fpuAllowed" [ at x; at y ])
                     (at x === at y)));
      ]
  in
  let v = var "v" and q = var "q" in
  [
    carrier_type;
    entry_ra;
    entries_ra;
    R.Member.field ~loc
      (R.Ident.make ~loc array_entries)
      (R.Type.named ~loc (local array_entries_ra) []);
    (* The entry at [i] with [v] and fraction [q]. *)
    func ~inline:true array_entry
      [ typed "i" int; typed "v" carrier; typed "q" real ]
      "m" entries_t
      ~body:(R.Expr.compr ~loc key (R.Expr.ite ~loc (k === i) (chunk v q) none));
    R.Member.free (func array_length [ typed "a" ref_ ] "r" int);
    axiom "array_lengths"
      (let length = call array_length [ a ] in
       R.Expr.forall ~loc ~triggers:[ [ length ] ]
         [ typed "a" ref_ ]
         (zero <== length &&& (length <== R.Expr.int ~loc max_array_length)));
    proc array_make
      [ typed "n" int; typed "d" carrier ]
      [ typed "a" ref_ ]
      [
        zero <== n &&& (n <== R.Expr.int ~loc max_array_length);
        R.Expr.call ~loc (value "holds") [ var "d" ];
      ]
      [
        call array_length [ a ] === n
        &&& own_entries
              (R.Expr.compr ~loc key
                 (R.Expr.ite ~loc (zero <== k &&& (k <<< n)) (chunk (var "d") one) none));
      ];
    proc array_read
      [ typed "a" ref_; typed "i" int; ghost "v" carrier; ghost "q" real ]
      [ typed "r" carrier ]
      [ own_entries (call array_entry [ i; v; q ]) ]
      [ own_entries (call array_entry [ i; v; q ]) &&& (var "r" === v) ];
    proc array_write
      [ typed "a" ref_; typed "i" int; typed "w" carrier; ghost "v" carrier ]
      []
      [
        own_entries (call array_entry [ i; v; one ]);
        R.Expr.call ~loc (value "holds") [ var "w" ];
      ]
      [ own_entries (call array_entry [ i; var "w"; one ]) ];
  ]

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
      ([ field "ref_contents"; field "atomic" ] @ array_members);
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
let value_dictionary_with_interfaces ~implements ~loc ~parameters ~name ~carrier
    ~unrestricted ~body ~members =
  let ident text = R.Ident.make ~loc text in
  let variable text = R.Expr.var ~loc (R.Name.make ~loc text) in
  let own_carrier = R.Type.named ~loc (R.Name.make ~loc "Carrier") [] in
  R.Member.module_ ~loc ~params:parameters ~implements (ident name)
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

let value_dictionary_with_members ~loc ~parameters ~name ~carrier ~unrestricted ~body
    ~members =
  value_dictionary_with_interfaces
    ~implements:[ (R.Name.make ~loc value_interface, []) ]
    ~loc ~parameters ~name ~carrier ~unrestricted ~body ~members

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
  let modulus =
    R.Expr.binary ~loc Plus
      (R.Expr.binary ~loc Minus (R.Expr.int ~loc max_int) (R.Expr.int ~loc min_int))
      (R.Expr.int ~loc 1)
  in
  [
    value_signature;
    unspecified_member;
    R.Member.callable
      (R.Callable.func ~loc ~inline:true
         ~formals:[ int_var "x" ]
         ~returns:[ R.Var.make ~loc (R.Ident.make ~loc "b") (R.Type.bool ~loc) ]
         (R.Ident.make ~loc in_range)
         (Some (R.Expr.binary ~loc And (bound Geq min_int) (bound Leq max_int))));
    (* One correction suffices for sums, differences, negations and machine quotients. *)
    R.Member.callable
      (R.Callable.func ~loc ~inline:true
         ~formals:[ int_var "x" ]
         ~returns:[ int_var "w" ]
         (R.Ident.make ~loc wrap)
         (Some
            (let n i = R.Expr.int ~loc i in
             R.Expr.ite ~loc
               (R.Expr.binary ~loc Gt x (n max_int))
               (R.Expr.binary ~loc Minus x modulus)
               (R.Expr.ite ~loc
                  (R.Expr.binary ~loc Lt x (n min_int))
                  (R.Expr.binary ~loc Plus x modulus)
                  x))));
    R.Member.callable
      (R.Callable.func ~loc ~inline:true
         ~formals:[ int_var "x" ]
         ~returns:[ int_var "w" ]
         (R.Ident.make ~loc wrap_full)
         (Some
            (let n i = R.Expr.int ~loc i in
             let normalized =
               R.Expr.binary ~loc Plus
                 (R.Expr.binary ~loc Mod (R.Expr.binary ~loc Minus x (n min_int)) modulus)
                 (n min_int)
             in
             R.Expr.ite ~loc
               (R.Expr.binary ~loc And (bound Geq min_int) (bound Leq max_int))
               x normalized)));
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
