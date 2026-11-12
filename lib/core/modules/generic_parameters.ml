(** Dictionary parameters shared by generic proof declarations. *)

open Base

let ( let* ) result f = Result.bind result ~f

type t = {
  key : string;
  member : string;
  name : string;
  loc : Location.t;
  parameters : Types.type_expr list;
  variables : Types.type_expr list;
  explicit : int;
}

let aggregate = function
  | [] -> Predef.type_unit
  | [ typ ] -> typ
  | types -> Ctype.newty (Ttuple (List.map types ~f:(fun typ -> (None, typ))))

let discover ?(expand = Fn.id) ?(project = Polymorphic_functions.source_arguments) ~key
    ~name ~at ~explicit parameters =
  let* scheme =
    Polymorphic_functions.discover ~expand ~project ~at (aggregate parameters)
  in
  Ok
    {
      key;
      member = (Qualified_name.of_string key).name;
      name;
      loc = at;
      parameters;
      variables = scheme.variables;
      explicit;
    }

let find ?target predicates key =
  List.find predicates ~f:(fun predicate ->
      String.equal predicate.key key
      || Option.exists target ~f:(fun target ->
          String.equal predicate.key target
          ||
          let owner = (Qualified_name.of_string predicate.name).path in
          String.equal target (String.concat ~sep:"." (owner @ [ predicate.member ]))))

let member predicate = predicate.member

let rebind ?(project = Polymorphic_functions.source_arguments) ~expand ~at declaration
    parameters =
  let* rebound =
    discover ~expand ~project ~key:declaration.key ~name:declaration.name ~at
      ~explicit:declaration.explicit parameters
  in
  let retained = List.concat_map parameters ~f:Polymorphic_functions.all_variables in
  let mismatch () =
    Report.unsupported at "A generic proof signature with different type parameters"
  in
  if
    List.for_all declaration.variables ~f:(fun variable ->
        List.mem retained variable ~equal:Types.eq_type)
  then
    if
      List.for_all rebound.variables ~f:(fun variable ->
          List.mem declaration.variables variable ~equal:Types.eq_type)
    then Ok { declaration with parameters }
    else mismatch ()
  else if
    List.exists declaration.variables ~f:(fun variable ->
        List.mem retained variable ~equal:Types.eq_type
        && not (List.mem rebound.variables variable ~equal:Types.eq_type))
  then
    Report.unsupported at
      "A generic proof signature with partially retained type parameters"
  else if List.length rebound.variables = List.length declaration.variables then
    Ok { rebound with member = declaration.member }
  else mismatch ()

let parameter_types predicate arguments =
  let substitutions = List.zip_exn predicate.variables arguments in
  let rec substitute typ =
    match List.Assoc.find substitutions typ ~equal:Types.eq_type with
    | Some typ -> typ
    | None ->
        begin match Types.get_desc typ with
        | Tvar _ | Tunivar _ -> typ
        | desc -> Ctype.newty (Compiler_types.map_desc substitute desc)
        end
  in
  List.map predicate.parameters ~f:substitute

let instantiate ?environment ?(opaque = fun _ -> false)
    ?(project = Polymorphic_functions.source_arguments) ~expand ~at predicate actuals =
  (* Compiler elaboration can lower recorded quantifiers' levels. *)
  let variables =
    List.map predicate.variables ~f:(fun variable ->
        match Types.get_desc variable with
        | (Tvar _ | Tunivar _) when Types.get_level variable <> Btype.generic_level ->
            Btype.newgenty (Types.get_desc variable)
        | _ -> variable)
  in
  let predicate =
    { predicate with parameters = parameter_types predicate variables; variables }
  in
  let canonical typ =
    let typ =
      Option.value_map environment ~default:typ ~f:(fun environment ->
          if opaque typ then typ
          else Ctype.expand_head environment (Compiler_types.scheme_structure typ))
    in
    match (environment, Types.get_desc typ) with
    | Some environment, Tconstr (path, arguments, _) ->
        begin match Env.try_normalize_type_path None environment path with
        | Some path -> Ctype.newconstr path arguments
        | None -> typ
        end
    | _ -> typ
  in
  let expand typ = canonical (expand (canonical typ)) in
  if List.length actuals > List.length predicate.parameters then
    Report.unsupported at "This polymorphic predicate arity"
  else
    let pairs =
      List.filter_map
        (List.zip_exn (List.take predicate.parameters (List.length actuals)) actuals)
        ~f:(fun (formal, actual) -> Option.map actual ~f:(fun actual -> (formal, actual)))
    in
    let formal, actual = List.unzip pairs in
    let declaration = aggregate formal and occurrence = aggregate actual in
    let* scheme = Polymorphic_functions.discover ~expand ~project ~at declaration in
    let* inferred =
      Polymorphic_functions.instantiate ~expand ~project ~at scheme ~declaration
        ~occurrence
    in
    let substitutions = List.zip_exn scheme.variables inferred in
    List.map predicate.variables ~f:(fun variable ->
        match List.Assoc.find substitutions variable ~equal:Types.eq_type with
        | Some actual -> Ok actual
        | None ->
            Report.unsupported at
              "A predicate type parameter not determined by its supplied arguments")
    |> Result.all

let types ?environment predicate types =
  List.mapi predicate.variables ~f:(fun index variable ->
      let data =
        Datatypes.variable_type ~variable
          ~owner:(String.split predicate.name ~on:'.')
          ~parameter:("A" ^ Int.to_string index)
          ~at:predicate.loc
      in
      Option.value_map environment ~default:data ~f:(fun environment ->
          Datatypes.bind_local_variable environment data))
  @ types
