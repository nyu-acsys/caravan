open Base
module C = Caravan_core
module S = Caravan_spec.Spec_ast
module R = Raven_api

let qualid components =
  match components with
  | [] -> failwith "expected a qualified name"
  | first :: rest ->
      List.fold rest
        ~init:(S.Qid (S.mk_id ~loc:Location.none first))
        ~f:(fun parent component -> S.Qdot (parent, S.mk_id ~loc:Location.none component))

let () =
  List.iter
    [ [ "f" ]; [ "A"; "f" ]; [ "A"; "B"; "f" ]; [ "A"; "List"; "length" ] ]
    ~f:(fun components ->
      let q = qualid components in
      let spelling = String.concat ~sep:"." components in
      let name = C.Qualified_name.of_spec q in
      assert (String.equal (C.Qualified_name.to_string name) spelling);
      assert (Poly.equal name (C.Qualified_name.of_string spelling));
      assert (String.equal (C.Translate_context.qualid_key q) spelling);
      let rec longident_components = function
        | Longident.Lident name -> [ name ]
        | Ldot (parent, name) -> longident_components parent.txt @ [ name.txt ]
        | Lapply _ -> failwith "unexpected applied module path"
      in
      assert (Poly.equal (longident_components (C.Source.longident q)) components);
      let printed name = R.Expr.to_string (R.Expr.var ~loc:R.Loc.none name) in
      assert (
        String.equal (printed (C.Qualified_name.raven ~loc:R.Loc.none name)) spelling);
      assert (
        String.equal
          (printed (C.Translate_context.qualified_name ~loc:R.Loc.none spelling))
          spelling));
  assert (
    Option.is_none (C.Translate_context.list_function (qualid [ "A"; "List"; "length" ])));
  assert (
    Poly.equal
      (C.Translate_context.list_function (qualid [ "List"; "length" ]))
      (Some "len"))

let () =
  let first = Path.Pident (Ident.create_local "f") in
  let second = Path.Pident (Ident.create_local "f") in
  let unknown = Path.Pident (Ident.create_local "f") in
  let functions = C.Path_bindings.of_list [ (first, "first"); (second, "second") ] in
  assert (Poly.equal (C.Path_bindings.find functions first) (Some "first"));
  assert (Poly.equal (C.Path_bindings.find functions second) (Some "second"));
  assert (not (C.Path_bindings.mem functions unknown));
  let extended = C.Path_bindings.add functions first "replacement" in
  assert (Poly.equal (C.Path_bindings.find extended first) (Some "replacement"));
  assert (Poly.equal (C.Path_bindings.find extended second) (Some "second"));
  assert (Poly.equal (C.Path_bindings.find functions first) (Some "first"));
  let root = Path.Pident (Ident.create_local "M") in
  let other_root = Path.Pident (Ident.create_local "M") in
  let nested = Path.Pdot (root, "N") in
  let libraries = C.Path_bindings.of_list [ (root, [ "M" ]); (nested, [ "M"; "N" ]) ] in
  let resolve = C.Translate_context.resolved_call functions libraries in
  assert (Poly.equal (resolve first) (Some "first"));
  assert (Poly.equal (resolve second) (Some "second"));
  assert (Poly.equal (resolve (Path.Pdot (root, "f"))) (Some "M.f"));
  assert (Poly.equal (resolve (Path.Pdot (nested, "f"))) (Some "M.N.f"));
  assert (Option.is_none (resolve unknown));
  assert (Option.is_none (resolve (Path.Pdot (other_root, "f"))));
  assert (Option.is_none (resolve (Path.Pdot (Path.Pdot (other_root, "N"), "f"))));
  assert (Option.is_none (resolve (Path.Papply (root, other_root))));
  assert (Option.is_none (resolve (Path.Pdot (Path.Papply (root, other_root), "f"))));
  assert (Option.is_none (C.Path_bindings.member libraries root))

let () =
  let standard = Path.Pident (Ident.create_persistent "Stdlib") in
  let shadow = Path.Pident (Ident.create_local "Stdlib") in
  assert (
    Poly.equal (C.Translate_context.stdlib_name (Path.Pdot (standard, "+"))) (Some "+"));
  assert (Option.is_none (C.Translate_context.stdlib_name (Path.Pdot (shadow, "+"))));
  assert (
    Poly.equal
      (C.Translate_context.atomic_name
         (Path.Pdot (Path.Pdot (standard, "Atomic"), "get")))
      (Some "get"));
  assert (
    Option.is_none
      (C.Translate_context.atomic_name (Path.Pdot (Path.Pdot (shadow, "Atomic"), "get"))));
  let atomic = Path.Pident (Ident.create_persistent "Stdlib__Atomic") in
  let shadow_atomic = Path.Pident (Ident.create_local "Stdlib__Atomic") in
  assert (
    Poly.equal (C.Translate_context.atomic_name (Path.Pdot (atomic, "get"))) (Some "get"));
  assert (
    Option.is_none (C.Translate_context.atomic_name (Path.Pdot (shadow_atomic, "get"))))

let location ?(file = "scope.ml") start stop =
  let position offset = { Lexing.dummy_pos with pos_fname = file; pos_cnum = offset } in
  { Location.loc_start = position start; loc_end = position stop; loc_ghost = false }

let () =
  let scope : C.Declaration_scope.t = { location = location 10 100 } in
  let item_loc = location 20 40 in
  let follows ?(next = None) at =
    C.Declaration_scope.following ~scope ~item_loc ~next at
  in
  assert (follows (location 40 100));
  assert (not (follows (location 39 60)));
  assert (not (follows (location 80 101)));
  assert (not (follows (location 101 120)));
  assert (follows (location ~file:"remapped.ml" 40 60));
  assert (follows ~next:(Some (location 80 90)) (location 60 80));
  assert (not (follows ~next:(Some (location 80 90)) (location 60 81)));
  let annotation text loc : C.Annotation.t =
    { text; loc; origin = None; outline = None }
  in
  let contract at = annotation "result = f x ensures result = x" at in
  let inside = location 40 100 in
  let outside = location 101 120 in
  let found annotations =
    match C.Procedures.contract_after ~scope annotations ~item_loc ~next:None with
    | Ok contract -> Option.is_some contract
    | Error _ -> failwith "expected one well-formed contract"
  in
  assert (found [ contract inside ]);
  assert (found [ contract inside; contract outside ]);
  assert (not (found [ contract outside ]));
  List.iter [ "manual"; "trusted" ] ~f:(fun text ->
      let marked annotations =
        if String.equal text "manual" then
          C.Procedures.manual_after ~scope annotations ~item_loc ~next:None
        else C.Procedures.trusted_after ~scope annotations ~item_loc ~next:None
      in
      assert (marked [ annotation text inside ]);
      assert (not (marked [ annotation text outside ])))
