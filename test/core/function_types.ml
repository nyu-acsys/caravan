open Base
open Types

let value_type t =
  match Caravan_core.Translate.argument_value_type t with
  | Some t -> t
  | None -> failwith "expected an unquantified argument scheme"

let () =
  let variable = Btype.newgenvar () in
  let list = Btype.newgenty (Tconstr (Predef.path_list, [ variable ], ref Mnil)) in
  let scheme = Btype.newgenmono list in
  let function_type = Btype.newgenty (Tarrow (Nolabel, scheme, variable, commu_ok)) in
  assert (Types.eq_type (value_type list) list);
  let extracted = value_type scheme in
  assert (Types.eq_type extracted list);
  begin match Types.get_desc extracted with
  | Tconstr (_, [ element ], _) -> assert (Types.eq_type element variable)
  | _ -> failwith "expected a list type"
  end;
  begin match Types.get_desc function_type with
  | Tarrow (_, argument, result, _) ->
      assert (Types.eq_type argument scheme);
      assert (Types.eq_type result variable);
      begin match Types.get_desc argument with
      | Tpoly (body, []) -> assert (Types.eq_type body list)
      | _ -> failwith "the arrow argument scheme was changed"
      end
  | _ -> failwith "expected a function type"
  end

let () =
  let variable = Btype.newgenty (Tunivar (Some "a")) in
  let quantified = Btype.newgenty (Tpoly (variable, [ variable ])) in
  assert (Option.is_none (Caravan_core.Translate.argument_value_type quantified));
  begin match Types.get_desc quantified with
  | Tpoly (body, [ bound ]) ->
      assert (Types.eq_type body variable);
      assert (Types.eq_type bound variable)
  | _ -> failwith "the quantified argument scheme was changed"
  end
