(** Dictionary-indexed proof resource families. *)

open Base
open Source_core

let rebase_worker ~namespace worker =
  String.concat ~sep:"." (namespace @ [ (Qualified_name.of_string worker).name ])

let rebase_family ~namespace ~scope (family : Datatypes.family) =
  { family with worker = rebase_worker ~namespace family.worker; scope }

let rec rebase_resource ~namespace ~scope resource =
  let descriptor (data : Datatypes.t) =
    { data with family = Option.map data.family ~f:(rebase_family ~namespace ~scope) }
  in
  {
    resource with
    resource_descriptor = descriptor resource.resource_descriptor;
    resource_aliases = List.map resource.resource_aliases ~f:descriptor;
    resource_public =
      Option.map resource.resource_public ~f:(rebase_resource ~namespace ~scope);
  }

let resource_worker resource =
  Option.some_if
    (not (List.is_empty resource.resource_parameters))
    Generic_parameters.
      {
        key = resource.resource_backend;
        member = (Qualified_name.of_string resource.resource_backend).name;
        name =
          Option.value_map resource.resource_descriptor.family
            ~default:(resource.resource_backend ^ "$Family") ~f:(fun family ->
              family.Datatypes.worker);
        loc = resource.resource_at;
        parameters = resource.resource_parameters;
        variables = resource.resource_parameters;
        explicit = List.length resource.resource_parameters;
      }

let alias_name (data : Datatypes.t) =
  match data.library with
  | Some (Path.Pdot (_, member)) -> member
  | _ ->
      Option.value
        (List.find_map data.paths ~f:(function
          | Path.Pdot (_, member) -> Some member
          | Pident _ | Papply _ | Pextra_ty _ -> None))
        ~default:data.module_name

let alias_member resource alias =
  "Type$" ^ (Qualified_name.of_string resource.resource_backend).name ^ "$" ^ alias

let dictionary_name resource member =
  "Values$" ^ (Qualified_name.of_string resource.resource_backend).name ^ "$" ^ member

let decorate_resource resource =
  match resource_worker resource with
  | None -> resource
  | Some worker ->
      let family member_name dictionary =
        Some
          {
            Datatypes.worker = worker.name;
            member = member_name;
            dictionary;
            scope = (Qualified_name.of_string worker.name).path;
            argument_projection = None;
          }
      in
      let descriptor =
        {
          resource.resource_descriptor with
          Datatypes.parameters = resource.resource_parameters;
          family = family (worker.member ^ ".T") (dictionary_name resource "t");
        }
      in
      let aliases =
        List.map resource.resource_aliases ~f:(fun data ->
            let alias = alias_name data in
            {
              data with
              Datatypes.parameters = resource.resource_parameters;
              family =
                family (alias_member resource alias) (dictionary_name resource alias);
            })
      in
      { resource with resource_descriptor = descriptor; resource_aliases = aliases }

let operation_worker resource ~name ~inputs ~result =
  Option.map (resource_worker resource) ~f:(fun worker ->
      {
        worker with
        Generic_parameters.member = worker.member ^ "." ^ name;
        parameters = inputs @ [ result ];
        explicit = List.length inputs;
      })

let apply_resource resource arguments =
  let arguments = if List.is_empty resource.resource_parameters then [] else arguments in
  Datatypes.instantiate_alias resource.resource_parameters arguments
    resource.resource_type

let native_module types resource arguments =
  match resource_worker resource with
  | None -> Some resource.resource_backend
  | Some worker ->
      Option.map (Datatypes.family_instance types resource.resource_descriptor arguments)
        ~f:(fun instance -> instance.family_name ^ "." ^ worker.member)

let find_resource resources path =
  Option.first_some
    (List.find resources ~f:(fun resource -> Path.same resource.resource_path path))
    (List.find resources ~f:(fun resource -> resource_has_path resource path))

let local_resource ~scope resources resource =
  let template =
    Option.value_map resource.resource_application ~default:resource.resource_id ~f:snd
  in
  Option.value
    (List.find resources ~f:(fun candidate ->
         Option.is_none candidate.resource_application
         && Option.equal Path.same candidate.resource_scope scope
         && Ident.same candidate.resource_id template))
    ~default:resource

let argument_types resources resource =
  let argument path =
    find_resource resources path
    |> Option.bind ~f:(fun target ->
        let target = local_resource ~scope:resource.resource_scope resources target in
        apply_resource target resource.resource_parameters)
  in
  Option.to_list (Option.bind resource.resource_alias_of ~f:argument)
  @ List.filter_map resource.resource_arguments ~f:(function
    | Type_argument typ -> Some typ
    | Module_argument path -> argument path)

(** The visible resource representative determines a carrier's native namespace. *)
let types resources data =
  List.concat_map resources ~f:(fun resource ->
      if Option.is_some resource.resource_descriptor.family then
        resource.resource_descriptor :: resource.resource_aliases
      else [])
  @ data

(** A protected-resource carrier made public by an explicit type equality. *)
let transparent_protected_resource resource =
  resource.resource_definition
  && Option.is_some resource.resource_descriptor.alias
  && (List.equal String.equal resource.resource_functor
        [ Mutex_contract.resource_interface ]
     || List.equal String.equal resource.resource_functor
          [ Mutex_visibility_contract.resource_interface ])

(** Manifest carrier constraints use a refined interface at the public boundary. *)
let interface_name resource =
  if resource.resource_definition && Option.is_some resource.resource_descriptor.alias
  then
    let name = Qualified_name.of_string resource.resource_backend in
    Qualified_name.to_string { name with name = name.name ^ "$Interface" }
  else String.concat ~sep:"." resource.resource_functor

(** The protected carrier fixes an instance even for operations taking only handles. *)
let protected_carrier resources resource =
  let rec follow seen resource arguments =
    if List.mem seen resource.resource_id ~equal:Ident.same then None
    else
      let seen = resource.resource_id :: seen in
      let actual path =
        Option.bind (find_resource resources path) ~f:(fun target ->
            follow seen target arguments)
      in
      if
        List.equal String.equal resource.resource_functor
          [ Mutex_contract.resource_interface ]
        || List.equal String.equal resource.resource_functor
             [ Mutex_visibility_contract.resource_interface ]
      then
        Option.bind resource.resource_descriptor.alias
          ~f:(Datatypes.instantiate_alias resource.resource_parameters arguments)
      else
        match resource.resource_alias_of with
        | Some path -> actual path
        | None
          when List.equal String.equal resource.resource_functor
                 [ Mutex_contract.protocol_name ]
               || List.equal String.equal resource.resource_functor
                    [ Mutex_visibility_contract.protocol_name ] ->
            List.find_map resource.resource_arguments ~f:(function
              | Module_argument path -> actual path
              | Type_argument _ -> None)
        | None -> None
  in
  follow [] resource resource.resource_parameters

let infer_protected_arguments ?(fallback = []) ~types ~environment ~at resources resource
    candidates =
  let ( let* ) result f = Result.bind result ~f in
  match resource_worker resource with
  | None -> Ok []
  | Some worker -> (
      let* carrier =
        Report.expect ~at "The protected resource family's carrier"
          (protected_carrier resources resource)
      in
      let probe = { worker with parameters = [ carrier ]; explicit = 1 } in
      let expand = Datatypes.expand types in
      let equal = List.equal (Polymorphic_functions.same_type ~expand) in
      let infer candidates =
        List.filter_map candidates ~f:(fun candidate ->
            Result.ok
              (Generic_parameters.instantiate ~environment
                 ~opaque:(Datatypes.is_opaque types) ~expand
                 ~project:(Datatypes.representation_arguments types)
                 ~at probe [ Some candidate ]))
        |> List.fold ~init:[] ~f:(fun choices arguments ->
            if List.mem choices arguments ~equal then choices else arguments :: choices)
      in
      let choices =
        match infer candidates with [] -> infer fallback | choices -> choices
      in
      match choices with
      | [ arguments ] -> Ok arguments
      | [] ->
          Error
            (Report.error Type at
               "Cannot infer the protected resource family from this operation's carrier \
                types")
      | _ ->
          Error
            (Report.error Type at
               "The protected resource family instance is ambiguous in this operation"))
