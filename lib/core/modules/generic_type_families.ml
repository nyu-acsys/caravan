(** Dictionary factories for abstract type constructors in module parameters. *)

open Base
module R = Raven_api

let arity declaration = List.length declaration.Typedtree.typ_params

let transparent declaration =
  arity declaration > 0 && Option.is_some declaration.Typedtree.typ_manifest

let interface_name count =
  Fresh_names.for_key
    ~key:("source-value-family:" ^ Int.to_string count)
    ("Ocaml_Value_Family_" ^ Int.to_string count)

let factory_name ~world ~member =
  Fresh_names.for_key
    ~key:("source-type-constructor:" ^ world ^ ":" ^ member)
    ("Type_" ^ world ^ "_" ^ member)

let parameters ~loc count =
  List.init count ~f:(fun index ->
      ( R.Ident.make ~loc ("A" ^ Int.to_string index),
        Qualified_name.raven ~loc (Qualified_name.of_string Prelude.value_interface) ))

let arguments ~loc count =
  List.init count ~f:(fun index ->
      R.Type.named ~loc (R.Name.make ~loc ("A" ^ Int.to_string index)) [])

let context ~owner ~types declaration =
  let variables =
    List.map declaration.Typedtree.typ_params ~f:(fun (p, _) -> p.ctyp_type)
  in
  let descriptors =
    List.mapi variables ~f:(fun index variable ->
        Datatypes.variable_type ~variable ~owner
          ~parameter:("A" ^ Int.to_string index)
          ~at:declaration.typ_loc)
  in
  (descriptors @ types, Ctype.newconstr (Path.Pident declaration.typ_id) variables)

let facade ~loc ~owner =
  let name member = R.Name.make ~loc ~path:owner member in
  Prelude.value_dictionary ~loc ~name:"Self"
    ~carrier:(R.Type.named ~loc (name "Carrier") [])
    ~unrestricted:(R.Expr.call ~loc (name "unrestricted") [])
    ~body:(R.Expr.call ~loc (name "holds") [ R.Expr.var ~loc (R.Name.make ~loc "value") ])

let signature count =
  let loc = Datatypes.loc Location.none in
  let name = interface_name count in
  R.Member.module_ ~loc ~interface:true ~params:(parameters ~loc count)
    ~implements:
      [
        (Qualified_name.raven ~loc (Qualified_name.of_string Prelude.value_interface), []);
      ]
    (R.Ident.make ~loc name)
    [ facade ~loc ~owner:[ name ] ]

let implementation ~loc ~owner ~types ~name declaration ~support =
  let ( let* ) = Result.( >>= ) in
  let namespace = owner @ [ name ] in
  let types, applied = context ~owner:namespace ~types declaration in
  let* carrier = Datatypes.typ types ~at:declaration.typ_loc applied in
  let* dictionary =
    Report.expect ~at:declaration.typ_loc "The value dictionary of a type constructor"
      (Datatypes.dictionary_name types applied)
  in
  let call member args =
    R.Expr.call ~loc
      (Qualified_name.raven ~loc (Qualified_name.of_string (dictionary ^ "." ^ member)))
      args
  in
  Ok
    (Prelude.value_dictionary_with_interfaces ~loc
       ~implements:
         [
           ( R.Name.make ~loc (interface_name (arity declaration)),
             arguments ~loc (arity declaration) );
         ]
       ~parameters:(parameters ~loc (arity declaration))
       ~name ~carrier ~unrestricted:(call "unrestricted" [])
       ~body:(call "holds" [ R.Expr.var ~loc (R.Name.make ~loc "value") ])
       ~members:support)
