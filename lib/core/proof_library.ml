open Base
module L = Checked_signatures

let ( let* ) = Result.( >>= )

let signatures at =
  match L.standard_library () with
  | Ok signatures -> Ok signatures
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
  let operations = constructors @ inherited in
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

let ocaml_type ~at ~(signature : L.module_signature) ~substitutions typ =
  let named name =
    Ast_helper.Typ.constr ~loc:at { txt = Longident.Lident name; loc = at } []
  in
  let unsupported message = Error (Report.error Unsupported at message) in
  let rec convert = function
    | L.Bool -> Ok (named "bool")
    | Int -> Ok (named "int")
    | Real -> Ok (named "float")
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
        | [ "T" ] -> Ok (named "t")
        | [ parameter; "T" ] | [ parameter ] ->
            begin match List.Assoc.find substitutions parameter ~equal:String.equal with
            | Some typ -> Ok typ
            | None ->
                if
                  List.exists signature.types ~f:(fun member ->
                      String.equal member.name parameter)
                then Ok (named (String.uncapitalize parameter))
                else
                  unsupported
                    ("Unsupported Raven library type " ^ String.concat ~sep:"." path)
            end
        | _ ->
            unsupported ("Unsupported Raven library type " ^ String.concat ~sep:"." path)
        end
  in
  convert typ

let operation_type ~at ~(signature : L.module_signature) ~substitutions
    (operation : L.operation) =
  let convert = ocaml_type ~at ~signature ~substitutions in
  let* inputs = Result.all (List.map operation.inputs ~f:(fun (_, typ) -> convert typ)) in
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
