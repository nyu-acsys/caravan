(** Nominal shared-field tags and their equalities in generic module contracts. *)

open Base
open Translate_context

let ( let* ) = Result.( >>= )

type parameter_slot = { name : string; member : string; field : Field_disciplines.t }

let parameter_slots inventory (signature : Module_inventory.signature_view) =
  let* slots =
    List.map signature.signature_types ~f:(fun (member, declaration) ->
        let* fields =
          Field_disciplines.of_declaration (Path.Pident declaration.Typedtree.typ_id)
            declaration.typ_type
        in
        Ok
          (List.filter_map fields ~f:(fun field ->
               let origin =
                 Module_inventory.field_origin inventory ~record_path:field.record_path
                   ~position:field.position
               in
               let kind =
                 Option.value_map origin ~default:field.kind ~f:(fun origin ->
                     origin.Field_disciplines.kind)
               in
               match kind with
               | Ordinary when not field.immutable -> None
               | Ordinary | Frozen | Relaxed ->
                   let constructor =
                     match field.record_path with
                     | Pextra_ty (_, Pcstr_ty constructor) -> [ constructor ]
                     | _ -> []
                   in
                   Some
                     {
                       member;
                       field =
                         {
                           field with
                           kind;
                           raw =
                             Option.value_map origin ~default:field.raw ~f:(fun origin ->
                                 origin.raw);
                         };
                       name =
                         Frozen_fields.kind_prefix kind
                         ^ "Tag$"
                         ^ Datatypes.framed ((member :: constructor) @ [ field.label ]);
                     })))
    |> Result.all
  in
  Ok (List.concat slots)

let slot_path owner slot =
  let path = Path.Pdot (owner, slot.member) in
  match slot.field.record_path with
  | Pextra_ty (_, extra) -> Path.Pextra_ty (path, extra)
  | _ -> path

let parameter_path (binding : Module_inventory.checked_binding) slot =
  Subst.type_path binding.parameter_substitution (slot_path binding.actual_path slot)

type root = { stage : Generic_modules.t; slot : parameter_slot; name : string }
type target = Fixed of string | Formal of root

type binding = {
  stage : Generic_modules.t;
  slot : parameter_slot;
  canonical : Path.t;
  target : target;
}

type group_plan = {
  group : Generic_modules.t;
  bindings : binding list;
  roots : root list;
}

type t = group_plan list

let plan ~fields ~inventory ~types groups =
  List.map groups ~f:(fun group ->
      let stages = Generic_modules.parameter_groups group in
      let formal (stage : Generic_modules.t) =
        match stage.representative.template.mod_desc with
        | Tmod_functor (Named (Some id, _, _), _) -> Some id
        | Tmod_functor (Unit, _)
        | Tmod_functor (Named (None, _, _), _)
        | Tmod_structure _ | Tmod_ident _ | Tmod_apply _ | Tmod_apply_unit _
        | Tmod_constraint _ | Tmod_unpack _ ->
            None
      in
      (* The final formal body includes all preceding parameter equations. *)
      let environment =
        match group.Generic_modules.representative.template.mod_desc with
        | Tmod_functor (_, body) -> body.mod_env
        | _ -> group.representative.template.mod_env
      in
      let parameter_ids = List.filter_map stages ~f:formal in
      let rec depends_on_parameter = function
        | Path.Pident id -> List.mem parameter_ids id ~equal:Ident.same
        | Pdot (parent, _) | Pextra_ty (parent, _) -> depends_on_parameter parent
        | Papply (fn, arg) -> depends_on_parameter fn || depends_on_parameter arg
      in
      let canonical stage slot =
        let declaration =
          List.Assoc.find_exn
            stage.Generic_modules.representative.argument.expected.signature_types
            slot.member ~equal:String.equal
        in
        let arguments =
          List.map declaration.typ_params ~f:(fun (typ, _) -> typ.Typedtree.ctyp_type)
        in
        let* parameter =
          match formal stage with
          | Some parameter -> Ok parameter
          | None ->
              Report.unsupported slot.field.at
                "A shared field parameter without a formal type environment"
        in
        let path = Path.Pdot (Path.Pident parameter, slot.member) in
        let* path =
          Signature_contract.compiler ~at:slot.field.at (fun () ->
              match
                Types.get_desc
                  (Ctype.expand_head environment (Ctype.newconstr path arguments))
              with
              | Tconstr (path, _, _) ->
                  Env.normalize_type_path (Some slot.field.at) environment path
              | _ -> path)
        in
        match slot.field.record_path with
        | Pextra_ty (_, extra) -> Ok (Path.Pextra_ty (path, extra))
        | _ -> Ok path
      in
      let* slots =
        List.map stages ~f:(fun stage ->
            let* slots =
              parameter_slots inventory
                stage.Generic_modules.representative.argument.expected
            in
            Ok (List.map slots ~f:(fun slot -> (stage, slot))))
        |> Result.all
      in
      let* bindings, roots =
        List.fold_result (List.concat slots) ~init:([], [])
          ~f:(fun (bindings, roots) (stage, slot) ->
            let* path = canonical stage slot in
            let previous =
              List.find bindings ~f:(fun (binding : binding) ->
                  Path.same path binding.canonical
                  && Field_disciplines.same_slot slot.field binding.slot.field)
            in
            let known =
              if depends_on_parameter path then None
              else
                Frozen_fields.find_tag fields ~inventory ~types ~record_path:path
                  ~position:slot.field.position ~label:slot.field.label
            in
            let target, roots =
              match (previous, known) with
              | Some binding, _ -> (binding.target, roots)
              | None, Some tag -> (Fixed tag, roots)
              | None, None ->
                  let root =
                    {
                      stage;
                      slot;
                      name =
                        Frozen_fields.kind_prefix slot.field.kind
                        ^ "Parameter$"
                        ^ Datatypes.framed [ stage.parameter; slot.name ];
                    }
                  in
                  (Formal root, root :: roots)
            in
            Ok ({ stage; slot; canonical = path; target } :: bindings, roots))
      in
      Ok { group; bindings = List.rev bindings; roots = List.rev roots })
  |> Result.all

let for_group plans (group : Generic_modules.t) =
  List.find_exn plans ~f:(fun plan ->
      String.equal plan.group.Generic_modules.name group.name)

let slot_binding plans (stage : Generic_modules.t) (slot : parameter_slot) =
  List.find_exn (for_group plans stage).bindings ~f:(fun binding ->
      String.equal binding.stage.interface stage.Generic_modules.interface
      && String.equal binding.slot.name slot.name)

let reference plans ~stage ~slot ~namespace =
  match (slot_binding plans stage slot).target with
  | Fixed tag -> tag
  | Formal root ->
      String.concat ~sep:"." (namespace @ [ root.stage.parameter; root.slot.name ])

let interface_reference plans ~stage ~slot =
  match (slot_binding plans stage slot).target with
  | Fixed tag -> tag
  | Formal root -> (
      match stage.Generic_modules.world with
      | Some world -> world ^ "." ^ root.name
      | None -> stage.interface ^ "." ^ root.slot.name)

let world_parameters plans group ~loc:l =
  List.map (for_group plans group).roots ~f:(fun root ->
      (ident ~loc:l root.name, qualified_name ~loc:l "Library.Type"))

let symbolic_tag plans ~inventory ~(context : Module_context.t) ~record_path ~position
    ~label =
  let project path = Subst.type_path context.projection path in
  let same_origin a b =
    Option.exists (Module_inventory.field_origin inventory ~record_path:a ~position)
      ~f:(fun left ->
        Option.exists (Module_inventory.field_origin inventory ~record_path:b ~position)
          ~f:(fun right -> Field_disciplines.same_field left right))
  in
  let* candidates =
    List.map context.parameters ~f:(fun parameter ->
        let group = parameter.Generic_proofs.generic in
        let* slots = parameter_slots inventory parameter.instance.argument.expected in
        Ok
          (List.filter_map slots ~f:(fun slot ->
               let owners =
                 Option.to_list
                   (Option.map parameter.original ~f:(fun id -> Path.Pident id))
                 @ parameter.instance.argument.paths @ group.representative.argument.paths
                 @ [ Path.Pident group.representative.parameter ]
               in
               if
                 not
                   (String.equal label slot.field.label
                   && Int.equal position slot.field.position)
               then None
               else
                 let exact =
                   List.exists owners ~f:(fun owner ->
                       Path.same (project record_path) (project (slot_path owner slot)))
                 in
                 let inherited =
                   List.exists owners ~f:(fun owner ->
                       same_origin record_path (slot_path owner slot))
                 in
                 Option.some_if (exact || inherited)
                   (exact, reference plans ~stage:group ~slot ~namespace:context.namespace))))
    |> Result.all
  in
  let candidates = List.concat candidates in
  let exact = List.filter candidates ~f:fst in
  let candidates =
    (if List.is_empty exact then candidates else exact)
    |> List.map ~f:snd
    |> List.stable_dedup ~compare:String.compare
  in
  match candidates with
  | [] -> Ok None
  | [ tag ] -> Ok (Some tag)
  | _ ->
      Report.unsupported context.scope.source_location
        ("An ambiguous symbolic shared-field family for " ^ label)

let actual_tag plans ~fields ~inventory ~types ?context ~path ~slot () =
  let* symbolic =
    match context with
    | None -> Ok None
    | Some context ->
        symbolic_tag plans ~inventory ~context ~record_path:path
          ~position:slot.field.position ~label:slot.field.label
  in
  let tag =
    Option.first_some symbolic
      (Frozen_fields.find_tag fields ~inventory ~types ~record_path:path
         ~position:slot.field.position ~label:slot.field.label)
  in
  Ok tag

let world_arguments plans ~fields ~inventory ~types ~contexts group application ~loc:l =
  List.map (for_group plans group).roots ~f:(fun root ->
      let parameter =
        List.find_exn application.Generic_modules.source.parameters ~f:(fun parameter ->
            Generic_modules.same_template root.stage.representative.template
              parameter.Module_inventory.template)
      in
      let binding = parameter.argument in
      let context = Module_context.for_location contexts binding.site.item_loc in
      let path = parameter_path binding root.slot in
      let* tag =
        actual_tag plans ~fields ~inventory ~types ~context ~path ~slot:root.slot ()
      in
      match tag with
      | Some tag -> Ok (R.Type.named ~loc:l (qualified_name ~loc:l tag) [])
      | None ->
          Report.unsupported binding.site.item_loc
            ("The "
            ^ Frozen_fields.kind_prefix root.slot.field.kind
            ^ " field family of " ^ root.slot.member ^ "." ^ root.slot.field.label
            ^ " in this module argument"))
  |> Result.all

let members plans ~fields ~inventory ~types ~group ?context ~binding ~aliases () =
  let* slots = parameter_slots inventory binding.Module_inventory.expected in
  let* members =
    List.map slots ~f:(fun slot ->
        let l = loc slot.field.at in
        let id = ident ~loc:l slot.name in
        let target =
          match (slot_binding plans group slot).target with
          | Fixed tag -> Some tag
          | Formal root ->
              begin match group.Generic_modules.world with
              | Some world -> Some (world ^ "." ^ root.name)
              | None ->
                  Option.some_if
                    (not (String.equal root.slot.name slot.name))
                    root.slot.name
              end
        in
        if aliases && Option.is_some target then Ok None
        else if not aliases then
          Ok
            (Some
               (match target with
               | None ->
                   R.Member.instance ~loc:l id (qualified_name ~loc:l "Library.Type")
               | Some tag -> R.Member.alias ~loc:l id (qualified_name ~loc:l tag)))
        else
          let path = parameter_path binding slot in
          let* tag = actual_tag plans ~fields ~inventory ~types ?context ~path ~slot () in
          match tag with
          | Some tag -> Ok (Some (R.Member.alias ~loc:l id (qualified_name ~loc:l tag)))
          | None ->
              Report.unsupported binding.site.item_loc
                ("The "
                ^ Frozen_fields.kind_prefix slot.field.kind
                ^ " field family of " ^ slot.member ^ "." ^ slot.field.label
                ^ " in this module argument"))
    |> Result.all
  in
  Ok (List.filter_opt members)
