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
}

let has_layout source =
  List.exists source.Module_inventory.declarations ~f:(fun declaration ->
      match declaration.Typedtree.typ_kind with
      | Ttype_variant _ | Ttype_record _ -> true
      | _ -> false)

let eligible (source : Module_inventory.specialization) =
  let signature = source.argument.expected in
  let abstract_types =
    List.for_all signature.signature_types ~f:(fun (_, declaration) ->
        match declaration.Typedtree.typ_kind with Ttype_abstract -> true | _ -> false)
  in
  let body =
    match source.template.mod_desc with
    | Tmod_functor ((Named (Some _, _, _) | Unit), { mod_desc = Tmod_structure body; _ })
      ->
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
        let rec heap_type t =
          let expanded =
            Signature_contract.compiler ~at:source.template.mod_loc (fun () ->
                Ctype.expand_head body.str_final_env t)
          in
          match Result.map expanded ~f:Types.get_desc with
          | Error _ -> true
          | Ok (Tconstr (path, args, _)) ->
              Datatypes.is_ref path || Datatypes.is_atomic path
              || List.exists args ~f:heap_type
          | Ok (Tarrow (_, a, b, _)) -> heap_type a || heap_type b
          | Ok (Ttuple args) -> List.exists args ~f:(fun (_, t) -> heap_type t)
          | Ok (Tpoly (t, _)) -> heap_type t
          | _ -> false
        in
        let expr iterator expression =
          if heap_type expression.Typedtree.exp_type then heap_access := true;
          begin match expression.exp_desc with
          | Texp_function _ when not (List.exists roots ~f:(phys_equal expression)) ->
              heap_access := true
          | _ -> ()
          end;
          Tast_iterator.default_iterator.expr iterator expression
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
    | _ -> false
  in
  (not (List.is_empty source.members)) && abstract_types && body

let plan ?(proof_layout = fun _ -> false) ~fresh sources =
  let application source =
    { source; name = fresh "Applied"; world = fresh "Selected"; layout = fresh "Layout" }
  in
  let add groups (source : Module_inventory.specialization) =
    match
      List.find groups ~f:(fun group ->
          phys_equal group.representative.template source.template)
    with
    | Some group ->
        List.map groups ~f:(fun other ->
            if phys_equal group other then
              { other with applications = other.applications @ [ application source ] }
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
            (has_layout source || proof_layout source)
            (fresh ("World_" ^ prefix))
        in
        let qualify leaf =
          Option.value_map world ~default:leaf ~f:(fun world -> world ^ "." ^ leaf)
        in
        groups
        @ [
            {
              name = qualify (fresh ("Generic_" ^ prefix));
              interface = qualify (fresh ("Argument_" ^ prefix));
              parameter = "Parameter";
              representative = source;
              applications = [ application source ];
              types = members source.argument.expected.signature_types "Type";
              resources = members source.argument.expected.signature_resources "resource";
              operations = members source.argument.expected.signature_values "operation";
              members = members source.members "method";
              world;
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
      Option.map
        (List.find group.applications ~f:(fun application ->
             phys_equal application.source.argument binding))
        ~f:(fun application -> (group, application)))

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
