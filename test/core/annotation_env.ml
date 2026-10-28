open Base
open Path
open Types
module C = Caravan_core

let get = function
  | Ok value -> value
  | Error (error : C.Report.error) -> failwith error.message

let scope source name =
  Option.value_exn (C.Proof_scopes.find_namespace source.C.Source.proof_scopes [ name ])

let runtime_type_id scope =
  List.find_map_exn scope.C.Proof_scopes.structure.str_items ~f:(fun item ->
      match item.Typedtree.str_desc with
      | Tstr_type (_, declaration :: _) -> Some declaration.typ_id
      | _ -> None)

let payload_input env =
  let _, value = Env.find_value_by_name (Longident.Lident "payload") env in
  let rec local_id typ =
    match Types.get_desc typ with
    | Tlink body | Tpoly (body, []) -> local_id body
    | Tconstr (Pident id, [], _) -> id
    | _ -> failwith "Expected a local type in the proof function input"
  in
  let rec input typ =
    match Types.get_desc typ with
    | Tpoly (body, _) | Tlink body -> input body
    | Tarrow (_, argument, _, _) -> local_id argument
    | _ -> failwith "Expected a proof function"
  in
  input value.val_type

let () =
  let source = get (C.Source.load "annotation_env_fixture.ml") in
  let _, boolean = Env.find_type_by_name (Longident.Lident "bool") source.env in
  let static = scope source "Static" in
  let static_type = runtime_type_id static in
  let shadowed =
    Env.add_type ~check:false (Ident.create_local "t") boolean
      static.structure.str_final_env
  in
  let environment = C.Source.annotation_env source ~at:static.source_location shadowed in
  assert (Ident.same (payload_input environment) static_type);
  let make = scope source "Make" in
  let parameter =
    match make.parameters with
    | [ Typedtree.Named (Some id, _, _) ] -> id
    | _ -> failwith "Expected one named functor parameter"
  in
  let declaration = Env.find_module (Pident parameter) make.structure.str_final_env in
  let representative_parameter = Ident.create_local "Cell" in
  let representative_type = Ident.create_local "t" in
  let original_type = runtime_type_id make in
  let original_declaration =
    Env.find_type (Pident original_type) make.structure.str_final_env
  in
  let lexical =
    Env.add_module_declaration ~check:false representative_parameter Mp_present
      declaration make.structure.str_final_env
    |> Env.add_type ~check:false representative_type original_declaration
    |> Env.add_type ~check:false (Ident.create_local "t") boolean
  in
  let environment = C.Source.annotation_env source ~at:make.source_location lexical in
  assert (Ident.same (payload_input environment) representative_type)
