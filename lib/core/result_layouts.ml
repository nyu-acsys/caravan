(** Result representations follow compiler application identities, independently of views.
*)

open Base

type t = {
  group : Generic_modules.t;
  application : Generic_modules.application;
  declaration : Typedtree.type_declaration;
  concrete : Datatypes.t;
  fields : Datatypes.field list;
}

let plan types groups =
  List.concat_map groups ~f:(fun group ->
      if Option.is_none group.Generic_modules.world then []
      else
        List.concat_map group.applications ~f:(fun application ->
            List.filter_map application.source.declarations ~f:(fun declaration ->
                match declaration.Typedtree.typ_kind with
                | Ttype_variant _ | Ttype_record _ ->
                    Option.map
                      (Datatypes.find types
                         (Path.Pdot (application.source.identity, declaration.typ_name.txt)))
                      ~f:(fun concrete ->
                        let representative =
                          Datatypes.find types
                            (Path.Pdot
                               (group.representative.identity, declaration.typ_name.txt))
                        in
                        let fields =
                          Option.value_map representative ~default:[] ~f:(fun d ->
                              Option.value d.Datatypes.heap ~default:[])
                        in
                        { group; application; declaration; concrete; fields })
                | _ -> None)))

let same_type a b = Option.equal Ident.same a.Datatypes.id b.Datatypes.id

let owner layouts entry =
  (List.find_exn layouts ~f:(fun other -> same_type entry.concrete other.concrete))
    .application

let data_name entry = "Data_" ^ entry.declaration.Typedtree.typ_name.txt

let descriptor entry ~owner =
  let source = Datatypes.of_declaration entry.declaration in
  Result.map source ~f:(fun source ->
      let module_name = data_name entry in
      let module_path = owner @ [ module_name ] in
      {
        source with
        module_name;
        module_path = Some module_path;
        backend_type =
          Option.some_if (Option.is_none source.heap)
            Qualified_name.{ path = module_path; name = "T" };
        heap =
          Option.map source.heap
            ~f:
              (List.map ~f:(fun (field : Datatypes.field) ->
                   let canonical =
                     List.find_exn entry.fields ~f:(fun candidate ->
                         String.equal candidate.Datatypes.label field.label)
                   in
                   {
                     field with
                     raven_field =
                       String.concat ~sep:"." (owner @ [ canonical.raven_field ]);
                   }));
      })

let concrete layouts types =
  List.map types ~f:(fun data ->
      match List.find layouts ~f:(fun entry -> same_type entry.concrete data) with
      | None -> Ok data
      | Some entry ->
          Result.map (descriptor entry ~owner:[ (owner layouts entry).layout ])
            ~f:(fun representation ->
              {
                data with
                module_path = representation.module_path;
                backend_type = representation.backend_type;
                ctors = representation.ctors;
                heap = representation.heap;
              }))
  |> Result.all

let symbolic layouts group ~owner =
  List.filter layouts ~f:(fun entry ->
      phys_equal entry.group group
      && phys_equal entry.application.source group.Generic_modules.representative)
  |> List.map ~f:(fun entry ->
      Result.map (descriptor entry ~owner) ~f:(fun data ->
          let paths =
            entry.concrete.paths
            @ Option.to_list (Option.map entry.concrete.id ~f:(fun id -> Path.Pident id))
          in
          Datatypes.with_paths data paths))
  |> Result.all

let contains layouts data =
  List.exists layouts ~f:(fun entry -> same_type entry.concrete data)

(** A declaration can precede its users once every required layout has been emitted. *)
let type_dependencies ?(additional = fun _ -> []) layouts types =
  let rec collect seen t =
    match Datatypes.desc types t with
    | Types.Tconstr (path, args, _) ->
        let arguments = List.concat_map args ~f:(collect seen) in
        if Datatypes.is_ref path || Datatypes.is_atomic path then []
        else
          begin match Datatypes.find types path with
          | Some { heap = Some _; _ } -> []
          | Some d when not (List.mem seen d.module_name ~equal:String.equal) ->
              let own =
                List.filter_map layouts ~f:(fun entry ->
                    Option.some_if (same_type entry.concrete d)
                      (owner layouts entry).layout)
              in
              own @ additional d @ arguments
              @ List.concat_map d.ctors ~f:(fun c ->
                  List.concat_map c.args ~f:(collect (d.module_name :: seen)))
          | _ -> arguments
          end
    | Ttuple items -> List.concat_map items ~f:(fun (_, t) -> collect seen t)
    | Tpoly (t, _) -> collect seen t
    | _ -> []
  in
  collect []

let dependencies ?additional layouts types data =
  let collect = type_dependencies ?additional layouts types in
  List.concat_map data.Datatypes.ctors ~f:(fun c -> List.concat_map c.args ~f:collect)
  @ List.concat_map (Option.value data.heap ~default:[]) ~f:(fun f -> collect f.typ)
