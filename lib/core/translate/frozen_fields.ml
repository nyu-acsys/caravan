(** Nominal tags and value-indexed instances of shared-field contracts. *)

open Base
open Translate_context

type family = {
  kind : Field_disciplines.kind;
  at : Location.t;
  payload : Types.type_expr;
  tag : string;
  name : string;
  dictionary : string;
  layout : bool;
}

type t = {
  immutable_storage : bool;
  tags : (Location.t * string * Field_disciplines.kind) list;
  bindings : (string * string) list;
  layout_tags : (Generic_modules.t * Location.t * string) list;
  families : family list;
  facades : (Access_fields.t * family) list;
}

let storage (data : Datatypes.t) label =
  Datatypes.framed
    (Option.value data.module_path ~default:[] @ [ data.module_name; label ])

let kind_prefix = function
  | Field_disciplines.Ordinary -> "Immutable"
  | kind -> String.capitalize (Field_disciplines.kind_name kind)

let layout_tag ~kind ~data_name ~constructor ~label =
  kind_prefix kind ^ "Tag$"
  ^ Datatypes.framed ((data_name :: Option.to_list constructor) @ [ label ])

let contract = function
  | Field_disciplines.Frozen ->
      ( Execution_contract.module_name ^ ".Frozen",
        Execution_contract.module_name ^ ".FrozenSignature" )
  | Relaxed -> (Relaxed_fields_contract.module_name, Relaxed_fields_contract.module_name)
  | Ordinary ->
      (Immutable_fields_contract.module_name, Immutable_fields_contract.module_name)

let plan ~(source : Source.t) ~inventory ~types ~layouts =
  let visibility = Source.visibility_required source in
  let canonicalize = Source.canonical_field_paths source.proof_scopes in
  let is_functor_location at =
    List.exists source.proof_scopes.scopes ~f:(fun scope ->
        (not (List.is_empty scope.parameters))
        && Declaration_scope.contains scope.source_location at)
  in
  let layout_fields =
    List.concat_map layouts ~f:(fun (entry : Result_layouts.t) ->
        if Option.is_some entry.declaration.typ_manifest then []
        else
          let layout = (Result_layouts.owner layouts entry).layout in
          Datatypes.all_fields entry.concrete
          |> List.filter_map ~f:(fun (slot : Datatypes.field) ->
              List.find_map inventory.Module_inventory.field_disciplines ~f:(fun field ->
                  let constructor =
                    match field.Field_disciplines.record_path with
                    | Path.Pextra_ty (_, Pcstr_ty name) -> Some name
                    | _ -> None
                  in
                  if
                    ((visibility && field.immutable)
                    || not (Poly.equal field.kind Ordinary))
                    && Declaration_scope.contains entry.declaration.typ_loc
                         field.declared_at
                    && String.equal field.label slot.label
                    && Option.equal String.equal constructor slot.constructor
                  then
                    let tag =
                      layout_tag ~kind:field.kind
                        ~data_name:(Result_layouts.data_name entry)
                        ~constructor ~label:field.label
                    in
                    Some
                      ( entry.group,
                        layout,
                        tag,
                        { field with value_type = slot.typ },
                        entry.concrete )
                  else None)))
  in
  let layout_tags =
    List.map layout_fields ~f:(fun (group, _, tag, field, _) -> (group, field.at, tag))
    |> List.stable_dedup ~compare:(fun (left, _, a) (right, _, b) ->
        let order = String.compare left.Generic_modules.name right.Generic_modules.name in
        if order = 0 then String.compare a b else order)
  in
  let declarations =
    List.filter_map inventory.Module_inventory.field_disciplines ~f:(fun field ->
        match field.Field_disciplines.kind with
        | Ordinary when not (visibility && field.immutable) -> None
        | Ordinary | Frozen | Relaxed ->
            let field =
              Option.value
                (Module_inventory.field_origin inventory ~record_path:field.record_path
                   ~position:field.position)
                ~default:field
            in
            let field = { field with record_path = canonicalize field.record_path } in
            Option.bind (Datatypes.find types field.record_path) ~f:(fun data ->
                Option.some_if
                  (Option.is_none data.library
                  && List.exists (Datatypes.all_fields data) ~f:(fun slot ->
                      String.equal slot.Datatypes.label field.label)
                  && not
                       (is_functor_location field.declared_at
                       || is_functor_location data.at
                       || List.exists layout_fields ~f:(fun (_, _, _, local, _) ->
                           Declaration_scope.same_place field.declared_at
                             local.declared_at)))
                  (storage data field.label, (field, data))))
    |> List.stable_dedup ~compare:(fun (left, _) (right, _) -> String.compare left right)
  in
  let declarations =
    List.map declarations ~f:(fun (key, (field, data)) -> (key, field, data, None))
    @ List.filter_map layout_fields ~f:(fun (group, layout, tag, field, concrete) ->
        if
          not
            (List.exists group.Generic_modules.applications ~f:(fun application ->
                 String.equal application.layout layout
                 && List.is_empty (Qualified_name.of_string layout).path))
        then None
        else
          Option.map
            (List.find types ~f:(Result_layouts.same_type concrete))
            ~f:(fun data ->
              let data =
                match field.record_path with
                | Pextra_ty (_, Pcstr_ty constructor) ->
                    { data with module_name = data.module_name ^ "$" ^ constructor }
                | _ -> data
              in
              (storage data field.label, field, data, Some (layout ^ "." ^ tag))))
    |> List.stable_dedup ~compare:(fun (left, _, _, l) (right, _, _, r) ->
        let order = String.compare left right in
        if order = 0 then Option.compare String.compare l r else order)
  in
  let tags, bindings, families, facades =
    List.fold declarations ~init:([], [], [], [])
      ~f:(fun (tags, bindings, families, facades) (key, field, data, layout_tag) ->
        let name =
          Fresh_names.fresh
            (kind_prefix field.Field_disciplines.kind
            ^ "Field$" ^ data.Datatypes.module_name ^ "$" ^ field.Field_disciplines.label
            )
        in
        let layout = Option.is_some layout_tag in
        let tag = Option.value layout_tag ~default:(name ^ "$Tag") in
        let dictionary payload =
          if List.is_empty (Polymorphic_functions.all_variables payload) then
            Datatypes.dictionary_name types payload
          else None
        in
        let selections =
          List.filter_map source.proof_access_fields ~f:(fun (facade : Access_fields.t) ->
              let selected_path =
                match Datatypes.desc types facade.owner_type with
                | Tconstr (path, _, _) ->
                    begin match facade.record_path with
                    | Pextra_ty (_, extra) -> Path.Pextra_ty (path, extra)
                    | _ -> path
                    end
                | _ -> facade.record_path
              in
              let matches path =
                Option.exists (Datatypes.find types path) ~f:(fun data ->
                    String.equal key (storage data facade.label.lbl_name))
              in
              if
                matches selected_path
                || (not layout)
                   && (matches facade.record_path
                      || Path.same field.record_path facade.record_path
                         && Int.equal field.position facade.label.lbl_pos)
              then
                Option.map (dictionary facade.value_type) ~f:(fun dict -> (facade, dict))
              else None)
        in
        let instances =
          List.filter_map
            (Field_disciplines.storage_type field
            :: List.map selections ~f:(fun (facade, _) -> facade.value_type))
            ~f:(fun payload ->
              Option.map (dictionary payload) ~f:(fun dict -> (dict, payload)))
          |> List.stable_dedup ~compare:(fun (left, _) (right, _) ->
              String.compare left right)
          |> List.mapi ~f:(fun index (dictionary, payload) ->
              {
                kind = field.kind;
                at = field.at;
                payload;
                tag;
                name = (if index = 0 then name else Fresh_names.fresh name);
                dictionary;
                layout;
              })
        in
        let aliases =
          List.map selections ~f:(fun (facade, dictionary) ->
              ( facade,
                List.find_exn instances ~f:(fun family ->
                    String.equal dictionary family.dictionary) ))
        in
        ( (if layout then tags else (field.at, tag, field.kind) :: tags),
          (key, tag) :: bindings,
          List.rev_append instances families,
          List.rev_append aliases facades ))
  in
  {
    immutable_storage =
      visibility
      && List.exists (inventory.field_disciplines @ source.signature_field_disciplines)
           ~f:(fun field -> field.immutable);
    tags = List.rev tags;
    bindings = List.rev bindings;
    layout_tags;
    families = List.rev families;
    facades = List.rev facades;
  }

let factory_name tag = tag ^ "$Family"

let tag_member ~loc:l tag =
  let id = ident ~loc:l in
  let tag_type = R.Type.data ~loc:l [ R.Type.variant ~loc:l (id "tag") [] ] in
  R.Member.module_ ~loc:l
    ~implements:[ (qualified_name ~loc:l "Library.Type", []) ]
    (id tag)
    [ R.Member.type_ ~loc:l ~rep:true (id "T") (Some tag_type) ]

let layout_members { layout_tags; _ } group ~abstract =
  List.filter_map layout_tags ~f:(fun (owner, at, tag) ->
      if not (phys_equal group owner) then None
      else
        let l = loc at in
        Some
          (if abstract then
             R.Member.instance ~loc:l (ident ~loc:l tag)
               (qualified_name ~loc:l "Library.Type")
           else tag_member ~loc:l tag))

let declarations { tags; immutable_storage; _ } =
  (if immutable_storage then [ Immutable_fields_contract.declaration () ] else [])
  @ List.concat_map tags ~f:(fun (at, tag, kind) ->
      let l = loc at in
      let id = ident ~loc:l in
      let q = qualified_name ~loc:l in
      let named name = R.Type.named ~loc:l (q name) [] in
      let implementation, signature = contract kind in
      [
        tag_member ~loc:l tag;
        R.Member.module_ ~loc:l
          ~params:[ (id "V", q Prelude.value_interface) ]
          (id (factory_name tag))
          [
            R.Member.instance ~loc:l
              ~def:(q implementation, [ named tag; named "V" ])
              (id "Field") (q signature);
          ];
      ])

let instances { families; facades; _ } =
  let instance family =
    let l = loc family.at in
    let q = qualified_name ~loc:l in
    let named name = R.Type.named ~loc:l (q name) [] in
    let factory, signature, args =
      if family.layout then
        let implementation, signature = contract family.kind in
        (q implementation, q signature, [ named family.tag; named family.dictionary ])
      else
        let factory = q (factory_name family.tag) in
        (factory, factory, [ named family.dictionary ])
    in
    R.Member.instance ~loc:l ~def:(factory, args) (ident ~loc:l family.name) signature
  in
  List.map families ~f:instance
  @ List.map facades ~f:(fun ((facade : Access_fields.t), family) ->
      let l = loc facade.at in
      let name =
        Fresh_names.fresh (kind_prefix family.kind ^ "Facade$" ^ facade.name.pid_str)
      in
      R.Member.alias ~loc:l (ident ~loc:l name)
        (qualified_name ~loc:l
           (if family.layout then family.name else family.name ^ ".Field")))

let find_tag plan ~inventory ~types ~record_path ~position ~label =
  let lookup path =
    Option.bind (Datatypes.find types path) ~f:(fun data ->
        List.Assoc.find plan.bindings (storage data label) ~equal:String.equal)
  in
  Option.first_some (lookup record_path)
    (Option.bind (Module_inventory.field_origin inventory ~record_path ~position)
       ~f:(fun origin -> lookup origin.record_path))
