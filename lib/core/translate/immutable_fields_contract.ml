(** Nominal storage for initialization-only fields of heap records. *)

module R = Raven_api

let module_name = "Ocaml_ImmutableField"

let declaration () =
  let loc = R.Loc.none in
  let name path text = R.Name.make ~loc ~path text in
  R.Member.module_ ~loc
    ~params:
      [
        (R.Ident.make ~loc "Tag", name [ "Library" ] "Type");
        (R.Ident.make ~loc "V", name [] Prelude.value_interface);
      ]
    (R.Ident.make ~loc module_name)
    [
      R.Member.field ~loc ~where:(name [ "V" ] "holds")
        (R.Ident.make ~loc "contents")
        (R.Type.named ~loc (name [ "V" ] "Carrier") []);
    ]
