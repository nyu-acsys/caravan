(** Dictionary instances of generalized ghost field declarations. *)

open Base

let worker (field : Source.proof_field) =
  let backend = Qualified_name.of_string field.field_backend in
  Generic_parameters.
    {
      key = field.field_backend;
      member = "proof$" ^ backend.name;
      name =
        Option.value field.field_family
          ~default:(String.concat ~sep:"." (backend.path @ [ "Field$" ^ backend.name ]));
      loc = field.field_at;
      parameters = [ field.field_owner; field.field_value ];
      variables = field.field_parameters;
      explicit = 2;
    }

let specialize ~types ~environment ~at ~owner ~value (field : Source.proof_field) =
  if List.is_empty field.field_parameters then Ok (None, field)
  else
    let worker = worker field in
    let ( let* ) = Result.( >>= ) in
    let* arguments =
      Generic_parameters.instantiate ~environment ~opaque:(Datatypes.is_opaque types)
        ~expand:(Datatypes.expand types) ~at worker [ owner; value ]
      |> Result.map_error ~f:(fun _ ->
          Report.error Type at
            "Cannot infer consistent type parameters for this ghost field from its owner \
             and stored value")
    in
    match Generic_parameters.parameter_types worker arguments with
    | [ field_owner; field_value ] ->
        Ok (Some (worker, arguments), { field with field_owner; field_value })
    | _ -> Report.unsupported at "This ghost field signature"
