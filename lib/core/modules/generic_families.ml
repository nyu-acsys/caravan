(** Mutually dependent generic declarations share one dictionary context. *)

open Base

type node = {
  name : string;
  scope : string list;
  variables : Types.type_expr list;
  at : Location.t;
  dependencies : string list;
}

type group = {
  name : string;
  scope : string list;
  variables : Types.type_expr list;
  at : Location.t;
  members : node list;
}

type t = { groups : group list; group_names : string Map.M(String).t }

let ( let* ) result f = Result.bind result ~f

let compatible (left : node) (right : node) =
  List.equal String.equal left.scope right.scope
  && List.length left.variables = List.length right.variables

let index_nodes nodes =
  List.fold_result nodes
    ~init:(Map.empty (module String))
    ~f:(fun nodes (node : node) ->
      match Map.find nodes node.name with
      | None -> Ok (Map.set nodes ~key:node.name ~data:node)
      | Some previous when compatible previous node ->
          Ok
            (Map.set nodes ~key:node.name
               ~data:
                 {
                   previous with
                   dependencies =
                     List.dedup_and_sort
                       (previous.dependencies @ node.dependencies)
                       ~compare:String.compare;
                 })
      | Some _ ->
          Report.unsupported node.at
            "A generic declaration with incompatible dictionary contexts")

type visit = Enter of string | Leave of string

let components graph =
  let successors graph name = Option.value (Map.find graph name) ~default:[] in
  let rec finish seen order = function
    | [] -> order
    | Enter name :: work when Set.mem seen name -> finish seen order work
    | Enter name :: work ->
        let work =
          List.fold (successors graph name) ~init:(Leave name :: work)
            ~f:(fun work name -> Enter name :: work)
        in
        finish (Set.add seen name) order work
    | Leave name :: work -> finish seen (name :: order) work
  in
  let order =
    finish
      (Set.empty (module String))
      []
      (List.map (Map.keys graph) ~f:(fun name -> Enter name))
  in
  let reverse =
    Map.fold graph
      ~init:(Map.map graph ~f:(fun _ -> []))
      ~f:(fun ~key:source ~data:targets reverse ->
        List.fold targets ~init:reverse ~f:(fun reverse target ->
            Map.update reverse target ~f:(fun previous ->
                source :: Option.value previous ~default:[])))
  in
  let rec collect seen members = function
    | [] -> (seen, members)
    | name :: work when Set.mem seen name -> collect seen members work
    | name :: work ->
        collect (Set.add seen name) (name :: members)
          (List.rev_append (successors reverse name) work)
  in
  List.fold order
    ~init:(Set.empty (module String), [])
    ~f:(fun (seen, groups) name ->
      if Set.mem seen name then (seen, groups)
      else
        let seen, members = collect seen [] [ name ] in
        (seen, members :: groups))
  |> snd

(** Dependencies outside the registered declarations do not participate in grouping. *)
let create nodes =
  let* nodes = index_nodes nodes in
  let prefixes =
    Map.keys nodes
    |> List.sort ~compare:(fun left right ->
        match Int.compare (String.length right) (String.length left) with
        | 0 -> String.compare left right
        | compared -> compared)
  in
  let dependency name =
    if Map.mem nodes name then Some name
    else
      List.find prefixes ~f:(fun prefix -> String.is_prefix name ~prefix:(prefix ^ "."))
  in
  let graph =
    Map.map nodes ~f:(fun node ->
        List.filter_map node.dependencies ~f:dependency
        |> List.dedup_and_sort ~compare:String.compare)
  in
  let* groups =
    Result.all
      (List.map (components graph) ~f:(fun members ->
           let members =
             List.sort members ~compare:String.compare |> List.map ~f:(Map.find_exn nodes)
           in
           let representative = List.hd_exn members in
           let* () =
             if List.for_all members ~f:(compatible representative) then Ok ()
             else
               Report.unsupported representative.at
                 "Mutually dependent generic declarations in different scopes or with \
                  different type parameter counts"
           in
           Ok
             {
               name = representative.name;
               scope = representative.scope;
               variables = representative.variables;
               at = representative.at;
               members;
             }))
  in
  let groups =
    List.sort groups ~compare:(fun left right -> String.compare left.name right.name)
  in
  let group_names =
    List.concat_map groups ~f:(fun group ->
        List.map group.members ~f:(fun member -> (member.name, group.name)))
    |> Map.of_alist_exn (module String)
  in
  Ok { groups; group_names }

let normalize_name groups name =
  match Map.find groups.group_names name with
  | Some representative -> representative
  | None ->
      Map.to_alist groups.group_names
      |> List.filter_map ~f:(fun (member, representative) ->
          Option.map
            (String.chop_prefix name ~prefix:(member ^ "."))
            ~f:(fun suffix -> (String.length member, representative ^ "." ^ suffix)))
      |> List.max_elt ~compare:(fun (left, _) (right, _) -> Int.compare left right)
      |> Option.value_map ~default:name ~f:snd
