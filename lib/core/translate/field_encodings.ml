(** Resolve ordinary field contracts using the current nominal module view. *)

open Base
open Translate_context

let ( let* ) = Result.( >>= )

let storage kind tag =
  match kind with
  | Field_disciplines.Frozen -> Frozen_storage tag
  | Relaxed -> Relaxed_storage tag
  | Ordinary -> Immutable_storage tag

let resolve ~fields ~parameters ~inventory ~disciplines ~types ~namespace ~at ~owner
    ~label =
  match Datatypes.desc types owner with
  | Tconstr (path, _, _) ->
      let data = Datatypes.find types path in
      let paths =
        Option.to_list (Option.bind data ~f:(fun data -> data.Datatypes.library))
        @ [ path ]
      in
      let candidates =
        List.concat_map parameters ~f:(fun plan ->
            List.filter_map plan.Frozen_parameters.bindings ~f:(fun binding ->
                let stage = binding.Frozen_parameters.stage in
                let slot = binding.slot in
                let interface = String.split stage.interface ~on:'.' in
                let worker = String.split plan.group.name ~on:'.' in
                let inside prefix =
                  List.is_prefix namespace ~prefix ~equal:String.equal
                in
                let relevant = inside interface || inside worker in
                let formal =
                  match stage.representative.template.mod_desc with
                  | Tmod_functor (Named (Some id, _, _), _) ->
                      [ Frozen_parameters.slot_path (Path.Pident id) slot ]
                  | _ -> []
                in
                let declared =
                  Frozen_parameters.slot_path stage.representative.argument.actual_path
                    slot
                  :: binding.canonical :: formal
                in
                if
                  relevant
                  && String.equal label slot.field.label
                  && List.exists paths ~f:(fun path ->
                      List.exists declared ~f:(Path.same path))
                then
                  Some
                    ( slot.field.kind,
                      if inside interface then
                        Frozen_parameters.interface_reference parameters ~stage ~slot
                      else
                        Frozen_parameters.reference parameters ~stage ~slot
                          ~namespace:worker )
                else None))
        |> List.stable_dedup ~compare:Poly.compare
      in
      begin match candidates with
      | [ (kind, tag) ] -> Ok (storage kind tag)
      | _ :: _ :: _ ->
          Report.unsupported at ("An ambiguous shared-field family for " ^ label)
      | [] -> (
          let metadata =
            List.find_map paths ~f:(fun path ->
                List.find_map inventory.Module_inventory.field_disciplines
                  ~f:(fun field ->
                    Option.some_if
                      ((Path.same path field.Field_disciplines.record_path
                       || Option.exists data ~f:(fun data ->
                           Datatypes.declares data field.record_path
                           || Declaration_scope.contains data.at field.declared_at))
                      && String.equal label field.label
                      &&
                      match (path, field.record_path) with
                      | Pextra_ty (_, Pcstr_ty left), Pextra_ty (_, Pcstr_ty right) ->
                          String.equal left right
                      | Pextra_ty _, _ | _, Pextra_ty _ -> false
                      | _ -> true)
                      field))
          in
          let* tag =
            match metadata with
            | None -> Ok None
            | Some field ->
                begin match field.kind with
                | Ordinary when not field.immutable -> Ok None
                | Ordinary | Frozen | Relaxed ->
                    let layout =
                      Option.bind data ~f:(fun data ->
                          Option.bind data.cell_namespace ~f:(fun owner ->
                              let constructor =
                                match path with
                                | Pextra_ty (_, Pcstr_ty constructor) -> Some constructor
                                | _ -> None
                              in
                              let data_name =
                                Option.value_map constructor ~default:data.module_name
                                  ~f:(fun constructor ->
                                    Option.value
                                      (String.chop_suffix data.module_name
                                         ~suffix:("$" ^ constructor))
                                      ~default:data.module_name)
                              in
                              let tag =
                                Frozen_fields.layout_tag ~kind:field.kind ~data_name
                                  ~constructor ~label
                              in
                              Option.some_if
                                (List.exists fields.Frozen_fields.layout_tags
                                   ~f:(fun (group, _, candidate) ->
                                     String.equal tag candidate
                                     && List.is_prefix namespace
                                          ~prefix:
                                            (String.split group.Generic_modules.name
                                               ~on:'.')
                                          ~equal:String.equal))
                                (String.concat ~sep:"." (owner @ [ tag ]))))
                    in
                    begin match
                      Option.first_some layout
                        (Frozen_fields.find_tag fields ~inventory ~types ~record_path:path
                           ~position:field.position ~label)
                    with
                    | Some tag -> Ok (Some tag)
                    | None ->
                        Report.unsupported at
                          ("The "
                          ^ Frozen_fields.kind_prefix field.kind
                          ^ " field family of " ^ label)
                    end
                end
          in
          match (tag, metadata) with
          | Some tag, Some field -> Ok (storage field.kind tag)
          | Some _, None | None, _ -> Ok Ordinary_storage)
      end
  | _ -> Ok Ordinary_storage
