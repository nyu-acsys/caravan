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

(** Apply an immutable type substitution to a supported runtime tree. *)
let typed_mapper ~f =
  let open Typedtree in
  let label (label : Data_types.label_description) =
    { label with lbl_res = f label.lbl_res; lbl_arg = f label.lbl_arg }
  in
  let constructor (constructor : Data_types.constructor_description) =
    {
      constructor with
      cstr_res = f constructor.cstr_res;
      cstr_args = List.map constructor.cstr_args ~f;
      cstr_existentials = List.map constructor.cstr_existentials ~f;
    }
  in
  let pat : type k.
      Tast_mapper.mapper -> k Typedtree.general_pattern -> k Typedtree.general_pattern =
   fun mapper pattern ->
    let pattern = Tast_mapper.default.pat mapper pattern in
    let pat_desc : k Typedtree.pattern_desc =
      match pattern.pat_desc with
      | Tpat_construct (name, description, patterns, extra) ->
          Tpat_construct (name, constructor description, patterns, extra)
      | Tpat_record (fields, closed) ->
          Tpat_record
            ( List.map fields ~f:(fun (name, description, pattern) ->
                  (name, label description, pattern)),
              closed )
      | description -> description
    in
    { pattern with pat_desc; pat_type = f pattern.pat_type }
  in
  {
    Tast_mapper.default with
    pat;
    typ =
      (fun mapper typ ->
        let typ = Tast_mapper.default.typ mapper typ in
        { typ with ctyp_type = f typ.ctyp_type });
    expr =
      (fun mapper expression ->
        let expression = Tast_mapper.default.expr mapper expression in
        let exp_desc =
          match expression.exp_desc with
          | Texp_ident (path, name, description) ->
              Texp_ident
                (path, name, { description with val_type = f description.val_type })
          | Texp_construct (name, description, arguments) ->
              Texp_construct (name, constructor description, arguments)
          | Texp_field (record, name, description) ->
              Texp_field (record, name, label description)
          | Texp_setfield (record, name, description, value) ->
              Texp_setfield (record, name, label description, value)
          | Texp_record record ->
              let fields =
                Array.map record.fields ~f:(fun (description, value) ->
                    let value =
                      match value with
                      | Typedtree.Kept (typ, mutable_) -> Typedtree.Kept (f typ, mutable_)
                      | Overridden _ -> value
                    in
                    (label description, value))
              in
              Texp_record { record with fields }
          | description -> description
        in
        { expression with exp_desc; exp_type = f expression.exp_type });
  }

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
