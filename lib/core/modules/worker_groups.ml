(** Generic declaration workers sharing one functor. Workers in the same scope with the
    same number of type parameters share one when their uses of each other apply them at
    their own parameters. A use at other arguments, of a worker of another shape, or of a
    generic module places the user in a later group, so the groups can be ordered and need
    not apply themselves. *)

open Base

let ( let* ) result f = Result.bind result ~f

type worker = { name : string; arity : int; witness : bool }
(** A worker with the number of its type parameters; a witness's takes its witness rather
    than their dictionaries, so it shares no functor. *)

type use = { namespace : string list; target : string; arguments : string list option }
(** A use of [target], a worker at the dictionaries [arguments] or a member of a module,
    in [namespace]. *)

type node = Worker of worker | Generic_module of string

let node_name = function Worker worker -> worker.name | Generic_module name -> name
let path name = String.split name ~on:'.'

let rec drop_prefix list ~prefix =
  match (prefix, list) with
  | [], rest -> Some rest
  | expected :: prefix, actual :: list when String.equal expected actual ->
      drop_prefix list ~prefix
  | _ -> None

(** The innermost node holding [namespace]. *)
let owner nodes namespace =
  List.filter nodes ~f:(fun node ->
      List.is_prefix namespace ~prefix:(path (node_name node)) ~equal:String.equal)
  |> List.max_elt ~compare:(fun left right ->
      Int.compare
        (List.length (path (node_name left)))
        (List.length (path (node_name right))))

(** Whether [user] may share a functor with [target], used at [arguments]. *)
let shareable user target arguments =
  match (user, target) with
  | Worker user, Worker target ->
      List.equal String.equal
        (List.drop_last_exn (path user.name))
        (List.drop_last_exn (path target.name))
      && user.arity = target.arity
      && List.equal String.equal arguments
           (List.init user.arity ~f:(fun index -> user.name ^ ".A" ^ Int.to_string index))
  | _ -> false

(** The uses between nodes, by user, with weight 0 when user and target may share a
    functor. [applications] maps the applications of generic modules to those modules. *)
let weighted_uses ~applications nodes uses =
  let resolve name =
    List.find_map applications ~f:(fun (application, generic) ->
        Option.map
          (drop_prefix (path name) ~prefix:(path application))
          ~f:(fun rest -> path generic @ rest))
    |> Option.value ~default:(path name)
  in
  List.fold uses
    ~init:(Map.empty (module String))
    ~f:(fun edges use ->
      match (owner nodes use.namespace, owner nodes (resolve use.target)) with
      | Some user, Some target when not (String.equal (node_name user) (node_name target))
        ->
          let weight =
            match use.arguments with
            | Some arguments
              when String.equal use.target (node_name target)
                   && shareable user target arguments ->
                0
            | Some _ | None -> 1
          in
          Map.update edges (node_name user) ~f:(fun previous ->
              let previous = Option.value previous ~default:[] in
              let earlier =
                Option.value
                  (List.Assoc.find previous (node_name target) ~equal:String.equal)
                  ~default:0
              in
              List.Assoc.add previous (node_name target) (Int.max earlier weight)
                ~equal:String.equal)
      | _ -> edges)

(** The groups of more than one worker, by their members' names. *)
let create ~generic_modules ~applications workers uses =
  let nodes =
    List.map workers ~f:(fun worker -> Worker worker)
    @ List.map generic_modules ~f:(fun name -> Generic_module name)
  in
  let edges = weighted_uses ~applications nodes uses in
  (* Each node's level, the heaviest path of uses from it: uses of weight 0 may be
     cyclic, as their nodes share a functor, but no cycle may have a heavier one. *)
  let names = List.map nodes ~f:node_name in
  let step levels =
    List.fold names ~init:levels ~f:(fun levels name ->
        let found =
          List.fold
            (Option.value (Map.find edges name) ~default:[])
            ~init:0
            ~f:(fun found (target, weight) ->
              Int.max found (Option.value (Map.find levels target) ~default:0 + weight))
        in
        Map.set levels ~key:name ~data:found)
  in
  let rec settle levels rounds =
    let next = step levels in
    if Map.equal Int.equal next levels then Ok levels
    else if rounds > List.length names then
      Report.internal Location.none "Cyclic uses of generic declaration workers"
    else settle next (rounds + 1)
  in
  let* levels =
    settle
      (Map.of_alist_reduce
         (module String)
         (List.map names ~f:(fun n -> (n, 0)))
         ~f:Int.max)
      0
  in
  let key worker =
    (List.drop_last_exn (path worker.name), worker.arity, Map.find_exn levels worker.name)
  in
  let compare_key (left_scope, left_arity, left_level)
      (right_scope, right_arity, right_level) =
    match List.compare String.compare left_scope right_scope with
    | 0 -> (
        match Int.compare left_arity right_arity with
        | 0 -> Int.compare left_level right_level
        | order -> order)
    | order -> order
  in
  let workers = List.filter workers ~f:(fun worker -> not worker.witness) in
  Ok
    (List.sort_and_group workers ~compare:(fun left right ->
         compare_key (key left) (key right))
    |> List.filter_map ~f:(function
      | _ :: _ :: _ as group -> Some (List.map group ~f:(fun worker -> worker.name))
      | _ -> None))
