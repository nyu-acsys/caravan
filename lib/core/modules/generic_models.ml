(** Mathematical datatypes whose payloads depend on dictionary-indexed families. *)

open Base

let name (data : Datatypes.t) =
  String.concat ~sep:"." (Option.value data.module_path ~default:[ data.module_name ])

let dependent types (data : Datatypes.t) =
  let rec visit seen typ =
    match Datatypes.desc types typ with
    | Tconstr (path, [ _ ], _) when Datatypes.is_ref path || Datatypes.is_atomic path ->
        false
    | Tconstr (path, arguments, _) ->
        List.exists arguments ~f:(visit seen)
        || Option.exists (Datatypes.find types path) ~f:(fun target ->
            Option.is_some target.family
            || (not (List.mem seen path ~equal:Path.same))
               && List.exists target.ctors ~f:(fun ctor ->
                   List.exists ctor.Datatypes.args ~f:(visit (path :: seen))))
    | Ttuple components -> List.exists components ~f:(fun (_, typ) -> visit seen typ)
    | Tpoly (body, []) -> visit seen body
    | _ -> false
  in
  data.mathematical && Option.is_none data.library && Option.is_none data.alias
  && (not (List.is_empty data.parameters))
  && List.exists data.ctors ~f:(fun ctor -> List.exists ctor.Datatypes.args ~f:(visit []))

let worker (data : Datatypes.t) =
  let key = name data in
  Generic_parameters.
    {
      key;
      member = "Model$" ^ (Qualified_name.of_string key).name;
      name =
        Option.value_map data.family ~default:(key ^ "$Family") ~f:(fun family ->
            family.Datatypes.worker);
      loc = data.at;
      parameters = data.parameters;
      variables = data.parameters;
      explicit = List.length data.parameters;
    }

let decorate plan data =
  let worker = worker data in
  let worker_name = Generic_family_plan.asset plan worker.key worker.name in
  {
    data with
    Datatypes.family =
      Some
        {
          worker = worker_name;
          member = worker.member ^ ".T";
          dictionary = "Values$" ^ worker.member;
          scope = (Qualified_name.of_string worker_name).path;
          argument_projection = None;
        };
  }

let members types data =
  let ( let* ) = Result.( >>= ) in
  let worker = worker data in
  let types = Generic_parameters.types worker types in
  let l = Datatypes.loc data.Datatypes.at in
  let* model =
    Datatypes.member ~parameters:false types { data with module_name = worker.member }
  in
  let carrier =
    Raven_api.Type.named ~loc:l
      (Qualified_name.raven ~loc:l
         (Qualified_name.of_string (worker.name ^ "." ^ worker.member ^ ".T")))
      []
  in
  let dictionary =
    Prelude.value_dictionary ~loc:l ~name:("Values$" ^ worker.member) ~carrier
      ~unrestricted:(Raven_api.Expr.bool ~loc:l true)
      ~body:(Raven_api.Expr.bool ~loc:l true)
  in
  Ok (worker, [ model; dictionary ])
