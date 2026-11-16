(** A conservative bound of one modeled atomic effect in an attributed source body. *)

open Base
open Translate_context
open State.Syntax

let reject at =
  State.of_result
    (error at "This operation is unsupported in a physically atomic source body")

let field ctx ~at ~owner (label : Data_types.label_description) =
  if Poly.equal label.lbl_mut Asttypes.Immutable then State.return 0
  else
    let* slot = State.field_of_label ctx.given ~at ~record_type:owner label in
    match slot with
    | Some (slot, true) ->
        let* frozen = State.frozen_storage ctx.given slot in
        let* relaxed = State.relaxed_storage ctx.given slot in
        if Option.is_some frozen || Option.is_some relaxed then State.return 1
        else reject at
    | Some (_, false) | None -> reject at

let application ctx (expression : Typedtree.expression) path =
  let at = expression.exp_loc in
  let* path = State.of_result (Source.normalize_value_path expression.exp_env ~at path) in
  match atomic_name path with
  | Some
      ("get" | "set" | "exchange" | "compare_and_set" | "fetch_and_add" | "incr" | "decr")
    ->
      State.return 1
  | Some _ -> reject at
  | None when Option.is_some (binop_of_path path) || Option.is_some (unop_of_path path) ->
      State.return 0
  | None ->
      begin match resolved_call ctx.given.functions ctx.given.libraries path with
      | Some name ->
          begin match
            List.Assoc.find ctx.given.procedure_signatures name ~equal:String.equal
          with
          | Some signature when signature.procedure_physical_atomic -> State.return 1
          | Some signature when signature.procedure_pure -> State.return 0
          | Some _ | None -> reject at
          end
      | None -> reject at
      end

let check ctx ~patterns body =
  let checks = ref [] in
  let add at check = checks := (at, check) :: !checks in
  let expr iterator (expression : Typedtree.expression) =
    let at = expression.exp_loc in
    begin match expression.exp_desc with
    | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _) ->
        add at (application ctx expression path)
    | Texp_field (owner, _, label) | Texp_setfield (owner, _, label, _) ->
        add at (field ctx ~at ~owner:owner.exp_type label)
    | Texp_ident _ | Texp_constant _ | Texp_let _ | Texp_tuple _ | Texp_construct _
    | Texp_variant _ | Texp_atomic_loc _ | Texp_ifthenelse _ | Texp_sequence _
    | Texp_assert _ | Texp_unreachable ->
        ()
    | Texp_match (_, cases, [], _) ->
        if
          List.exists cases ~f:(fun case ->
              Option.is_some (snd (Typedtree.split_pattern case.Typedtree.c_lhs)))
        then add at (reject at)
    | Texp_struct_item
        ({ str_desc = Tstr_open { open_expr = { mod_desc = Tmod_ident _; _ }; _ }; _ }, _)
      ->
        ()
    | Texp_apply _ | Texp_function _ | Texp_match _ | Texp_try _ | Texp_record _
    | Texp_array _ | Texp_while _ | Texp_for _ | Texp_send _ | Texp_new _ | Texp_instvar _
    | Texp_setinstvar _ | Texp_override _ | Texp_object _ | Texp_pack _ | Texp_letop _
    | Texp_lazy _ | Texp_extension_constructor _ | Texp_struct_item _ ->
        add at (reject at)
    end;
    Tast_iterator.default_iterator.expr iterator expression
  in
  let pat : type k. Tast_iterator.iterator -> k Typedtree.general_pattern -> unit =
   fun iterator pattern ->
    begin match pattern.pat_desc with
    | Tpat_record (fields, _) ->
        List.iter fields ~f:(fun (_, label, _) ->
            add pattern.pat_loc
              (field ctx ~at:pattern.pat_loc ~owner:pattern.pat_type label))
    | _ -> ()
    end;
    Tast_iterator.default_iterator.pat iterator pattern
  in
  let iterator = { Tast_iterator.default_iterator with expr; pat } in
  List.iter patterns ~f:(iterator.pat iterator);
  iterator.expr iterator body;
  let+ _ =
    State.fold (List.rev !checks) ~init:0 ~f:(fun count (at, check) ->
        let* effects = check in
        if count + effects <= 1 then State.return (count + effects)
        else
          State.of_result
            (error at
               "A physically atomic source body may perform at most one modeled atomic \
                effect"))
  in
  ()
