(** Effect restrictions carried by OCaml value declarations. *)

open Base

let local attributes =
  match
    List.filter attributes ~f:(fun attribute ->
        String.equal attribute.Parsetree.attr_name.txt "caravan.local")
  with
  | [] -> Ok false
  | [ { attr_payload = PStr []; _ } ] -> Ok true
  | attribute :: _ ->
      Report.unsupported attribute.attr_loc
        "A local attribute other than a single [@@caravan.local]"

let empty_opens attributes =
  match
    List.filter attributes ~f:(fun attribute ->
        String.equal attribute.Parsetree.attr_name.txt "caravan.opens")
  with
  | [] -> Ok None
  | [
   ({
      attr_payload =
        PStr
          [
            {
              pstr_desc =
                Pstr_eval
                  ({ pexp_desc = Pexp_construct ({ txt = Lident "[]"; _ }, None); _ }, _);
              _;
            };
          ];
      _;
    } as attribute);
  ] ->
      Ok (Some attribute.attr_loc)
  | attribute :: _ ->
      Report.unsupported attribute.attr_loc
        "An opens attribute other than [@@caravan.opens []]"
