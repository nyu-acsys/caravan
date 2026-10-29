(** Generic operation bodies with concrete source result representations kept separate. *)

open Base

type application = {
  source : Module_inventory.specialization;
  name : string;
  world : string;
  layout : string;
}

type t = {
  name : string;
  interface : string;
  parameter : string;
  representative : Module_inventory.specialization;
  applications : application list;
  types : (string * string) list;
  resources : (string * string) list;
  operations : (string * string) list;
  members : (string * string) list;
  world : string option;
  captures : t list;
}

let parameter_groups group = group.captures @ [ { group with captures = [] } ]

let stage_source (source : Module_inventory.specialization)
    (stage : Module_inventory.parameter_instance) =
  {
    source with
    template = stage.template;
    parameter = stage.parameter;
    argument = stage.argument;
  }

let same_template left right = Poly.equal left.Typedtree.mod_loc right.Typedtree.mod_loc

let same_stages (left : Module_inventory.specialization)
    (right : Module_inventory.specialization) =
  Option.equal Path.same left.origin right.origin
  && same_template left.Module_inventory.template right.template
  && List.equal
       (fun (first : Module_inventory.parameter_instance)
            (second : Module_inventory.parameter_instance) ->
         same_template first.template second.template)
       left.parameters right.parameters

let has_layout source =
  List.exists source.Module_inventory.declarations ~f:(fun declaration ->
      match declaration.Typedtree.typ_kind with
      | Ttype_variant _ | Ttype_record _ -> true
      | _ -> false)

let eligible (source : Module_inventory.specialization) =
  let abstract_types =
    List.for_all source.parameters
      ~f:(fun (stage : Module_inventory.parameter_instance) ->
        List.for_all stage.argument.expected.signature_types ~f:(fun (_, declaration) ->
            match declaration.Typedtree.typ_kind with
            | Ttype_abstract -> true
            | _ -> false))
  in
  let body =
    let direct_body =
      match source.template.mod_desc with
      | Tmod_functor ((Named (Some _, _, _) | Unit), body) ->
          Module_inventory.direct_body body
      | _ -> None
    in
    match direct_body with
    | Some body ->
        let heap_access = ref false in
        let bindings =
          List.concat_map body.str_items ~f:(fun item ->
              match item.Typedtree.str_desc with
              | Tstr_value (_, bindings) -> bindings
              | _ -> [])
        in
        let roots = List.map bindings ~f:(fun binding -> binding.Typedtree.vb_expr) in
        let names =
          List.filter_map bindings ~f:(fun binding ->
              match binding.Typedtree.vb_pat.pat_desc with
              | Tpat_var (id, _, _) -> Some (Ident.name id)
              | _ -> None)
        in
        let expanded_type t =
          let expanded =
            Signature_contract.compiler ~at:source.template.mod_loc (fun () ->
                Ctype.expand_head body.str_final_env t)
          in
          Result.map expanded ~f:Types.get_desc
        in
        let rec closed_heap_value_type t =
          match expanded_type t with
          | Ok (Tconstr (path, [], _)) ->
              Path.same path Predef.path_int
              || Path.same path Predef.path_bool
              || Path.same path Predef.path_unit
          | Ok (Tconstr (path, [ element ], _))
            when Path.same path Predef.path_list
                 || Path.same path Predef.path_option
                 || Datatypes.is_ref path || Datatypes.is_atomic path ->
              closed_heap_value_type element
          | Ok (Ttuple elements) ->
              List.for_all elements ~f:(fun (_, element) ->
                  closed_heap_value_type element)
          | Ok (Tpoly (element, [])) -> closed_heap_value_type element
          | Ok _ | Error _ -> false
        in
        let rec heap_type t =
          match expanded_type t with
          | Error _ -> true
          | Ok (Tconstr (path, [ element ], _))
            when Datatypes.is_ref path || Datatypes.is_atomic path ->
              not (closed_heap_value_type element)
          | Ok (Tconstr (path, args, _)) ->
              Datatypes.is_ref path || Datatypes.is_atomic path
              || List.exists args ~f:heap_type
          | Ok (Tarrow (_, a, b, _)) -> heap_type a || heap_type b
          | Ok (Ttuple args) -> List.exists args ~f:(fun (_, t) -> heap_type t)
          | Ok (Tpoly (t, _)) -> heap_type t
          | _ -> false
        in
        let expr (iterator : Tast_iterator.iterator) (expression : Typedtree.expression) =
          if heap_type expression.exp_type then heap_access := true;
          begin match expression.exp_desc with
          | Texp_function _ when not (List.exists roots ~f:(phys_equal expression)) ->
              heap_access := true
          | _ -> ()
          end;
          match expression.exp_desc with
          | Texp_apply (({ Typedtree.exp_desc = Texp_ident _; _ } as callee), _) ->
              let scoped =
                {
                  iterator with
                  expr =
                    (fun _ child ->
                      if not (phys_equal child callee) then iterator.expr iterator child);
                }
              in
              Tast_iterator.default_iterator.expr scoped expression
          | _ -> Tast_iterator.default_iterator.expr iterator expression
        in
        let iterator = { Tast_iterator.default_iterator with expr } in
        iterator.structure iterator body;
        (not !heap_access)
        && (not (List.contains_dup names ~compare:String.compare))
        && List.for_all body.str_items ~f:(fun item ->
            match item.Typedtree.str_desc with
            | Tstr_value _ | Tstr_attribute _ -> true
            | Tstr_type (_, declarations) ->
                List.for_all declarations ~f:(fun declaration ->
                    match declaration.Typedtree.typ_kind with
                    | Ttype_abstract -> Option.is_some declaration.typ_manifest
                    | Ttype_variant _ | Ttype_record _ ->
                        List.is_empty declaration.typ_params
                    | _ -> false)
            | _ -> false)
    | None -> false
  in
  (not (List.is_empty source.members)) && abstract_types && body

let plan ?(proof_layout = fun _ -> false) ~fresh sources =
  let make_application source =
    { source; name = fresh "Applied"; world = fresh "Selected"; layout = fresh "Layout" }
  in
  let add groups (source : Module_inventory.specialization) =
    let application = make_application source in
    match List.find groups ~f:(fun group -> same_stages group.representative source) with
    | Some group ->
        List.map groups ~f:(fun other ->
            if phys_equal group other then
              {
                other with
                applications = other.applications @ [ application ];
                captures =
                  List.map2_exn other.captures (List.drop_last_exn source.parameters)
                    ~f:(fun capture stage ->
                      {
                        capture with
                        applications =
                          capture.applications
                          @ [ { application with source = stage_source source stage } ];
                      });
              }
            else other)
    | None ->
        let prefix = String.concat ~sep:"_" source.argument.namespace in
        let members entries label =
          List.map entries ~f:(fun (member, _) ->
              let stem =
                String.map member ~f:(fun c ->
                    if Char.is_alphanum c || Char.equal c '_' then c else '_')
              in
              (member, fresh (label ^ "_" ^ stem)))
        in
        let world =
          Option.some_if
            (has_layout source || proof_layout source
            || List.length source.parameters > 1
               && List.exists source.parameters ~f:(fun parameter ->
                   (not
                      (List.is_empty
                         parameter.Module_inventory.argument.expected.signature_types))
                   || not
                        (List.is_empty parameter.argument.expected.signature_ghost_modules))
            )
            (fresh ("World_" ^ prefix))
        in
        let qualify leaf =
          Option.value_map world ~default:leaf ~f:(fun world -> world ^ "." ^ leaf)
        in
        let name = qualify (fresh ("Generic_" ^ prefix)) in
        let member_names = members source.members "method" in
        let capture (stage : Module_inventory.parameter_instance) index =
          let stage_source = stage_source source stage in
          {
            name;
            interface = qualify (fresh ("Argument_" ^ prefix ^ "_stage"));
            parameter = "Parameter_" ^ Int.to_string index;
            representative = stage_source;
            applications = [ { application with source = stage_source } ];
            types = members stage.argument.expected.signature_types "Type";
            resources = members stage.argument.expected.signature_resources "resource";
            operations = members stage.argument.expected.signature_values "operation";
            members = member_names;
            world;
            captures = [];
          }
        in
        let captures =
          List.mapi (List.drop_last_exn source.parameters) ~f:(fun index stage ->
              capture stage index)
        in
        groups
        @ [
            {
              name;
              interface = qualify (fresh ("Argument_" ^ prefix));
              parameter = "Parameter";
              representative = source;
              applications = [ application ];
              types = members source.argument.expected.signature_types "Type";
              resources = members source.argument.expected.signature_resources "resource";
              operations = members source.argument.expected.signature_values "operation";
              members = member_names;
              world;
              captures;
            };
          ]
  in
  List.fold (List.filter sources ~f:eligible) ~init:[] ~f:add

let interface (group : t) (application : application) =
  match group.world with
  | None -> group.interface
  | Some _ -> application.world ^ "." ^ (Qualified_name.of_string group.interface).name

let application_for_binding groups binding =
  List.find_map groups ~f:(fun group ->
      List.find_map (parameter_groups group) ~f:(fun stage ->
          Option.map
            (List.find stage.applications ~f:(fun application ->
                 phys_equal application.source.argument binding))
            ~f:(fun application -> (stage, application))))

let member groups id =
  List.find_map groups ~f:(fun group ->
      List.find_map group.applications ~f:(fun application ->
          Option.map
            (List.find application.source.members ~f:(fun (_, candidate) ->
                 Ident.same candidate id))
            ~f:(fun (source, _) ->
              let stem = List.Assoc.find_exn group.members source ~equal:String.equal in
              (group, application, stem))))

let types group ~owner =
  let formal_types =
    List.map group.representative.argument.expected.signature_types
      ~f:(fun (source, declaration) ->
        let backend =
          Qualified_name.
            {
              path = owner;
              name = List.Assoc.find_exn group.types source ~equal:String.equal;
            }
        in
        Datatypes.parameter_type ~parameter:group.representative.parameter ~name:source
          ~declaration ~backend)
  in
  let ghost_types =
    List.map group.representative.argument.expected.signature_ghost_modules
      ~f:(fun (name, ghost) ->
        let backend = Qualified_name.{ path = owner @ [ name ]; name = "T" } in
        let descriptor = ghost.Module_inventory.ghost_resource.resource_descriptor in
        {
          descriptor with
          Datatypes.id = None;
          module_path = Some (owner @ [ name ]);
          backend_type = Some backend;
          paths =
            Path.Pdot (Path.Pdot (Path.Pident group.representative.parameter, name), "t")
            :: descriptor.paths;
        })
  in
  formal_types @ ghost_types

let worker_types group ~owner =
  List.concat_map (parameter_groups group) ~f:(fun stage ->
      types stage ~owner:(owner @ [ stage.parameter ]))

let carrier_name group member = "Carrier_" ^ group.parameter ^ "_" ^ member
let algebra_name group member = "Algebra_" ^ group.parameter ^ "_" ^ member

let world_types group ~owner =
  let ordinary, ghosts = List.split_n (types group ~owner) (List.length group.types) in
  ordinary
  @ List.map2_exn group.representative.argument.expected.signature_ghost_modules ghosts
      ~f:(fun (member, _) descriptor ->
        let stem = carrier_name group member in
        {
          descriptor with
          Datatypes.module_path = Some (owner @ [ stem ]);
          backend_type = Some Qualified_name.{ path = owner; name = stem };
        })

let type_slots group =
  List.concat_map (parameter_groups group) ~f:(fun stage ->
      List.map stage.types ~f:snd
      @ List.map stage.representative.argument.expected.signature_ghost_modules
          ~f:(fun (member, _) -> carrier_name stage member))
