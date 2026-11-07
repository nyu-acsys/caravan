(** Local carrier dictionaries and family aliases in dependency order. *)

open Base
open Translate_context

type node = { name : string; member : R.Member.t; dependencies : string list }

let ( let* ) result f = Result.bind result ~f

let domain_dependencies requests =
  List.fold requests
    ~init:(Map.empty (module String))
    ~f:(fun dependencies request ->
      List.fold
        (Datatypes.family_domain_dependencies ~dictionaries:true request.domain_types
           [ request.domain_type ]) ~init:dependencies
        ~f:(fun dependencies (name, families) ->
          Map.update dependencies name ~f:(fun existing ->
              List.map families ~f:(fun family -> family.Datatypes.family_name)
              @ Option.value existing ~default:[])))

let order ~namespace ~at ~domains ~domain_dependencies
    ~(instances : function_instance list) =
  let local name =
    List.equal String.equal (Qualified_name.of_string name).path namespace
  in
  let domains =
    Datatypes.unique_domain_members domains
    |> List.filter ~f:(fun (name, _) -> local name)
  in
  let domains =
    List.map domains ~f:(fun (name, member) ->
        {
          name;
          member;
          dependencies = Option.value (Map.find domain_dependencies name) ~default:[];
        })
  in
  let instances =
    List.filter_map instances ~f:(fun instance ->
        Option.some_if
          (List.equal String.equal instance.instance_namespace namespace)
          {
            name = String.concat ~sep:"." (namespace @ [ instance.instance_name ]);
            member = Value_instances.member ~loc:(loc at) instance;
            dependencies = instance.instance_arguments;
          })
  in
  let nodes = domains @ instances in
  let prefixes =
    List.map nodes ~f:(fun node -> node.name)
    |> List.dedup_and_sort ~compare:(fun left right ->
        match Int.compare (String.length right) (String.length left) with
        | 0 -> String.compare left right
        | compared -> compared)
  in
  let resolve name =
    List.find prefixes ~f:(fun prefix ->
        String.equal prefix name || String.is_prefix name ~prefix:(prefix ^ "."))
  in
  let dependencies node =
    List.filter_map node.dependencies ~f:resolve
    |> List.filter ~f:(fun name -> not (String.equal name node.name))
    |> List.dedup_and_sort ~compare:String.compare
  in
  let* ordered =
    Polymorphic_functions.order_by nodes
      ~name:(fun node -> node.name)
      ~location:(fun _ -> at)
      ~dependencies
  in
  Ok (List.map ordered ~f:(fun node -> node.member))
