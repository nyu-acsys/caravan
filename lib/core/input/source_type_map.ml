(** Project related proof metadata through one compiler type group. *)

open Base
open Source_core

module Group = struct
  type 'a t = {
    collect : Types.type_expr list -> Types.type_expr list;
    read : Types.type_expr list -> 'a * Types.type_expr list;
  }

  let pure value = { collect = Fn.id; read = (fun types -> (value, types)) }

  let ( let+ ) item f =
    {
      item with
      read =
        (fun types ->
          let value, types = item.read types in
          (f value, types));
    }

  let ( and+ ) left right =
    {
      collect = (fun types -> left.collect (right.collect types));
      read =
        (fun types ->
          let left, types = left.read types in
          let right, types = right.read types in
          ((left, right), types));
    }

  let typ value =
    {
      collect = (fun types -> value :: types);
      read =
        (function
        | value :: types -> (value, types)
        | [] -> failwith "A type projection must preserve metadata group arity");
    }

  let list values ~f =
    List.fold_right values ~init:(pure []) ~f:(fun value rest ->
        let+ value = f value and+ rest = rest in
        value :: rest)

  let option value ~f =
    match value with
    | None -> pure None
    | Some value ->
        let+ value = f value in
        Some value

  let run schema ~f =
    let values = Compiler_types.map_group (schema.collect []) ~f in
    let result, remaining = schema.read values in
    if List.is_empty remaining then result
    else failwith "A type projection must preserve metadata group arity"
end

open Group

let label (label : Types.label_declaration) =
  let+ ld_type = typ label.ld_type in
  { label with ld_type }

let constructor (constructor : Types.constructor_declaration) =
  let arguments =
    match constructor.cd_args with
    | Types.Cstr_tuple types ->
        let+ types = list types ~f:typ in
        Types.Cstr_tuple types
    | Cstr_record labels ->
        let+ labels = list labels ~f:label in
        Types.Cstr_record labels
  in
  let+ cd_args = arguments and+ cd_res = option constructor.cd_res ~f:typ in
  { constructor with cd_args; cd_res }

let declaration (declaration : Types.type_declaration) =
  let kind =
    match declaration.type_kind with
    | Types.Type_record (labels, representation) ->
        let+ labels = list labels ~f:label in
        Types.Type_record (labels, representation)
    | Type_variant (constructors, representation) ->
        let+ constructors = list constructors ~f:constructor in
        Types.Type_variant (constructors, representation)
    | Type_abstract _ | Type_open | Type_external _ -> pure declaration.type_kind
  in
  let+ type_params = list declaration.type_params ~f:typ
  and+ type_manifest = option declaration.type_manifest ~f:typ
  and+ type_kind = kind in
  { declaration with type_params; type_manifest; type_kind }

let descriptor (data : Datatypes.t) =
  let+ parameters = list data.parameters ~f:typ
  and+ variable = option data.variable ~f:typ
  and+ alias = option data.alias ~f:typ
  and+ ctors =
    list data.ctors ~f:(fun ctor ->
        let+ args = list ctor.Datatypes.args ~f:typ in
        { ctor with args })
  and+ heap =
    option data.heap ~f:(fun fields ->
        list fields ~f:(fun field ->
            let+ typ = typ field.Datatypes.typ in
            { field with typ }))
  in
  { data with parameters; variable; alias; ctors; heap }

let rec resource_schema (resource : proof_resource) =
  let+ resource_parameters = list resource.resource_parameters ~f:typ
  and+ resource_representation = option resource.resource_representation ~f:typ
  and+ resource_type = typ resource.resource_type
  and+ resource_arguments =
    list resource.resource_arguments ~f:(function
      | Type_argument value ->
          let+ value = typ value in
          Type_argument value
      | Module_argument _ as argument -> pure argument)
  and+ resource_type_members =
    list resource.resource_type_members ~f:(fun (name, id, value) ->
        let+ value = declaration value in
        (name, id, value))
  and+ resource_operations =
    list resource.resource_operations ~f:(fun (name, inputs, output) ->
        let+ inputs = list inputs ~f:typ and+ output = typ output in
        (name, inputs, output))
  and+ resource_descriptor = descriptor resource.resource_descriptor
  and+ resource_aliases = list resource.resource_aliases ~f:descriptor
  and+ resource_public = option resource.resource_public ~f:resource_schema in
  {
    resource with
    resource_parameters;
    resource_representation;
    resource_type;
    resource_arguments;
    resource_type_members;
    resource_operations;
    resource_descriptor;
    resource_aliases;
    resource_public;
  }

let resource resource ~f = run (resource_schema resource) ~f

let field field ~f =
  let schema =
    let+ field_parameters = list field.field_parameters ~f:typ
    and+ field_owner = typ field.field_owner
    and+ field_value = typ field.field_value in
    { field with field_parameters; field_owner; field_value }
  in
  run schema ~f
