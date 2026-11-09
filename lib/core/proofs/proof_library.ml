open Base
module L = Checked_signatures

let ( let* ) = Result.( >>= )

let canonical_path = function
  | [ "Ghost"; "MutexResource" ] -> [ Mutex_contract.resource_interface ]
  | [ "Ghost"; "Mutex" ] -> [ Mutex_contract.protocol_name ]
  | path -> path

let mutex_signatures = Mutex_contract.source_signatures

let signatures at =
  match L.standard_library () with
  | Ok signatures -> Ok (signatures @ mutex_signatures ())
  | Error diagnostics ->
      let message =
        match diagnostics with
        | diagnostic :: _ -> diagnostic.Raven_api.Diagnostic.message
        | [] -> "Raven's standard library could not be checked"
      in
      Error (Report.error Type at message)

let path_of_qualid (qualid : Caravan_spec.Spec_ast.qualid) =
  let rec collect acc = function
    | Caravan_spec.Spec_ast.Qid id -> id.pid_str :: acc
    | Qdot (prefix, id) -> collect (id.pid_str :: acc) prefix
  in
  collect [] qualid

let find signatures path =
  let path = canonical_path path in
  List.find signatures ~f:(fun (signature : L.module_signature) ->
      List.equal String.equal signature.path path
      || List.equal String.equal signature.path ("Library" :: path))

let interface_paths signatures (signature : L.module_signature) =
  let rec collect seen path =
    let selected = find signatures path in
    let path = Option.value_map selected ~default:path ~f:(fun member -> member.path) in
    if List.exists seen ~f:(List.equal String.equal path) then seen
    else
      let seen = seen @ [ path ] in
      Option.value_map selected ~default:seen ~f:(fun member ->
          List.fold member.implements ~init:seen ~f:collect)
  in
  collect [] signature.path

let is_resource_algebra signatures signature =
  List.exists (interface_paths signatures signature) ~f:(fun path ->
      List.equal String.equal path [ "Library"; "ResourceAlgebra" ]
      || List.equal String.equal path [ "ResourceAlgebra" ])

let is_protected_resource signatures signature =
  List.exists (interface_paths signatures signature) ~f:(fun path ->
      List.equal String.equal path [ Mutex_contract.resource_interface ])

let is_mutex_protocol (signature : L.module_signature) =
  List.equal String.equal signature.path [ Mutex_contract.protocol_name ]

let is_resource_interface signatures signature =
  signature.L.interface
  && (is_resource_algebra signatures signature
     || is_protected_resource signatures signature)

let members signatures (signature : L.module_signature) ~get ~name =
  let rec collect visited (signature : L.module_signature) =
    if List.exists visited ~f:(List.equal String.equal signature.path) then []
    else
      let visited = signature.path :: visited in
      get signature
      @ List.concat_map signature.implements ~f:(fun path ->
          Option.value_map (find signatures path) ~default:[] ~f:(collect visited))
  in
  List.fold (collect [] signature) ~init:[] ~f:(fun seen member ->
      if List.exists seen ~f:(fun earlier -> String.equal (name earlier) (name member))
      then seen
      else seen @ [ member ])

let member_types signatures signature =
  members signatures signature
    ~get:(fun member -> member.L.types)
    ~name:(fun member -> member.L.name)

let member_constants signatures signature =
  members signatures signature ~get:(fun member -> member.L.constants) ~name:fst

let member_callables signatures signature =
  members signatures signature
    ~get:(fun member -> member.L.callables)
    ~name:(fun callable -> callable.L.operation.name)

let operation_kind signatures signature name =
  Option.value_map
    (List.find (member_callables signatures signature) ~f:(fun callable ->
         String.equal callable.L.operation.name name))
    ~default:Raven_api.Ast.Callable.Func
    ~f:(fun callable -> callable.kind)

let logical_predicate_operation (callable : L.callable) =
  match callable.kind with
  | Raven_api.Ast.Callable.Pred | Invariant ->
      Some
        {
          callable.operation with
          inputs = callable.operation.inputs @ callable.operation.outputs;
          outputs = [ ("result", L.Bool) ];
        }
  | Func | Proc | Lemma -> None

let member_operations signatures (signature : L.module_signature) =
  let types = member_types signatures signature in
  let constructors =
    List.concat_map types ~f:(fun typ -> typ.constructors @ typ.destructors)
  in
  let inherited =
    members signatures signature
      ~get:(fun member -> member.L.operations)
      ~name:(fun operation -> operation.L.name)
  in
  let ghost_operations =
    if is_protected_resource signatures signature || is_mutex_protocol signature then
      List.filter_map (member_callables signatures signature) ~f:(fun callable ->
          match callable.L.kind with
          | Raven_api.Ast.Callable.Pred | Invariant ->
              logical_predicate_operation callable
          | Lemma -> Some callable.operation
          | Func | Proc -> None)
    else []
  in
  let operations = constructors @ inherited @ ghost_operations in
  List.fold operations ~init:[] ~f:(fun seen operation ->
      if
        List.exists seen ~f:(fun (earlier : L.operation) ->
            String.equal earlier.name operation.name)
      then seen
      else seen @ [ operation ])

let accepts_type_argument signatures path =
  match find signatures path with
  | Some signature -> (
      List.is_empty signature.parameters
      && List.is_empty signature.required_members
      &&
      match signature.types with
      | [ { rep = true; definition = None; constructors = []; destructors = []; _ } ] ->
          true
      | _ -> false)
  | None -> false

let native_type ~at module_name =
  Ast_helper.Typ.constr ~loc:at
    {
      txt =
        Longident.Ldot
          ( {
              txt =
                Longident.Ldot
                  ( { txt = Longident.Lident "Stdlib"; loc = at },
                    { txt = module_name; loc = at } );
              loc = at;
            },
            { txt = "t"; loc = at } );
      loc = at;
    }
    []

let mutex_type ~at = native_type ~at "Mutex"
let condition_type ~at = native_type ~at "Condition"

let owner_type ~at =
  Ast_helper.Typ.constr ~loc:at
    {
      txt =
        Longident.Ldot
          ({ txt = Longident.Lident "Ghost"; loc = at }, { txt = "t"; loc = at });
      loc = at;
    }
    []

let ocaml_type ?(family_arguments = []) ~at ~(signature : L.module_signature)
    ~substitutions typ =
  let named ?(arguments = []) name =
    Ast_helper.Typ.constr ~loc:at { txt = Longident.Lident name; loc = at } arguments
  in
  let unsupported message = Error (Report.error Unsupported at message) in
  let rec convert = function
    | L.Bool -> Ok (named "bool")
    | Int -> Ok (named "int")
    | Real -> Ok (named "float")
    | Ref when is_mutex_protocol signature -> Ok (mutex_type ~at)
    | Ref -> unsupported "A Raven Ref type cannot be exposed to OCaml"
    | Tuple [] -> Ok (named "unit")
    | Tuple [ one ] -> convert one
    | Tuple members ->
        let* members = Result.all (List.map members ~f:convert) in
        Ok
          (Ast_helper.Typ.tuple ~loc:at
             (List.map members ~f:(fun member -> (None, member))))
    | Set member ->
        let* member = convert member in
        Ok
          (Ast_helper.Typ.constr ~loc:at
             { txt = Longident.Lident "set"; loc = at }
             [ member ])
    | FinSet member ->
        let* member = convert member in
        Ok
          (Ast_helper.Typ.constr ~loc:at
             { txt = Longident.Lident "finset"; loc = at }
             [ member ])
    | Map (key, value) ->
        let* key = convert key in
        let* value = convert value in
        Ok
          (Ast_helper.Typ.constr ~loc:at
             { txt = Longident.Lident "map"; loc = at }
             [ key; value ])
    | Other name -> unsupported ("Unsupported Raven library type " ^ name)
    | Named ([ path ], []) when String.equal path Condition_contract.type_name ->
        Ok (condition_type ~at)
    | Named (path, args) ->
        let owner =
          signature.path :: signature.implements
          |> List.find ~f:(fun prefix -> List.is_prefix path ~prefix ~equal:String.equal)
        in
        let path =
          Option.value_map owner ~default:path ~f:(fun prefix ->
              List.drop path (List.length prefix))
        in
        let* () =
          if List.is_empty args then Ok ()
          else
            unsupported ("Parameterized Raven library type " ^ String.concat ~sep:"." path)
        in
        begin match path with
        | [ "T" ] when is_mutex_protocol signature -> Ok (mutex_type ~at)
        | [ "T" ] -> Ok (named ~arguments:family_arguments "t")
        | [ parameter; "T" ] | [ parameter ] ->
            begin match List.Assoc.find substitutions parameter ~equal:String.equal with
            | Some typ -> Ok typ
            | None ->
                if
                  List.exists signature.types ~f:(fun member ->
                      String.equal member.name parameter)
                then
                  Ok (named ~arguments:family_arguments (String.uncapitalize parameter))
                else
                  unsupported
                    ("Unsupported Raven library type " ^ String.concat ~sep:"." path)
            end
        | _ ->
            unsupported ("Unsupported Raven library type " ^ String.concat ~sep:"." path)
        end
  in
  convert typ

let operation_type ?(family_arguments = []) ~at ~(signature : L.module_signature)
    ~substitutions (operation : L.operation) =
  let convert = ocaml_type ~family_arguments ~at ~signature ~substitutions in
  let* inputs =
    Result.all
      (List.map operation.inputs ~f:(fun (name, typ) ->
           if is_mutex_protocol signature && String.equal name "self" then
             Ok (owner_type ~at)
           else convert typ))
  in
  let* outputs =
    Result.all (List.map operation.outputs ~f:(fun (_, typ) -> convert typ))
  in
  let result =
    match outputs with
    | [] -> Ast_helper.Typ.constr ~loc:at { txt = Longident.Lident "unit"; loc = at } []
    | [ output ] -> output
    | outputs ->
        Ast_helper.Typ.tuple ~loc:at (List.map outputs ~f:(fun output -> (None, output)))
  in
  Ok
    (List.fold_right inputs ~init:result ~f:(fun input result ->
         Ast_helper.Typ.arrow ~loc:at Nolabel input result))

let callable_type ?(family_arguments = []) ~at ~(signature : L.module_signature)
    ~substitutions (callable : L.callable) =
  let operation =
    Option.value (logical_predicate_operation callable) ~default:callable.operation
  in
  operation_type ~family_arguments ~at ~signature ~substitutions operation
