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

let discover ?(expand = Fn.id) ~key ~name ~at ~explicit parameters =
  let* scheme = Polymorphic_functions.discover ~expand ~at (aggregate parameters) in
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

let rebind ~expand ~at declaration parameters =
  let* rebound =
    discover ~expand ~key:declaration.key ~name:declaration.name ~at
      ~explicit:declaration.explicit parameters
  in
  if List.length rebound.variables = List.length declaration.variables then
    Ok { rebound with member = declaration.member }
  else Report.unsupported at "A generic proof signature with different type parameters"

let instantiate ?environment ~expand ~at predicate actuals =
  let canonical typ =
    let typ =
      Option.value_map environment ~default:typ ~f:(fun environment ->
          Ctype.expand_head environment (Compiler_types.scheme_structure typ))
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
    let* scheme = Polymorphic_functions.discover ~expand ~at declaration in
    let* inferred =
      Polymorphic_functions.instantiate ~expand ~at scheme ~declaration ~occurrence
    in
    let substitutions = List.zip_exn scheme.variables inferred in
    List.map predicate.variables ~f:(fun variable ->
        match List.Assoc.find substitutions variable ~equal:Types.eq_type with
        | Some actual -> Ok actual
        | None ->
            Report.unsupported at
              "A predicate type parameter not determined by its supplied arguments")
    |> Result.all

let parameter_types predicate arguments =
  let substitutions = List.zip_exn predicate.variables arguments in
  let rec substitute typ =
    match List.Assoc.find substitutions typ ~equal:Types.eq_type with
    | Some typ -> typ
    | None ->
        begin match Types.get_desc typ with
        | Tvar _ | Tunivar _ -> typ
        | desc -> Ctype.newty (Btype.copy_type_desc substitute desc)
        end
  in
  List.map predicate.parameters ~f:substitute

let types predicate types =
  List.mapi predicate.variables ~f:(fun index variable ->
      Datatypes.variable_type ~variable
        ~owner:(String.split predicate.name ~on:'.')
        ~parameter:("A" ^ Int.to_string index)
        ~at:predicate.loc)
  @ types
