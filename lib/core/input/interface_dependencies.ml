(** Order selected interface sources using OCaml's module-dependency analysis. *)

open Base

let dependencies ~at signature =
  let previous = !Depend.free_structure_names in
  Depend.free_structure_names := Depend.String.Set.empty;
  let result =
    try
      Depend.add_signature Depend.String.Map.empty signature;
      Ok (Depend.String.Set.elements !Depend.free_structure_names)
    with exn ->
      Error
        (Option.value (Report.of_exn exn)
           ~default:(Report.error Type at (Stdlib.Printexc.to_string exn)))
  in
  Depend.free_structure_names := previous;
  result

let order entries ~name ~signature ~at =
  let ( let* ) result f = Result.bind result ~f in
  let* entries_with_dependencies =
    List.map entries ~f:(fun entry ->
        let* dependencies = dependencies ~at:(at entry) (signature entry) in
        Ok (name entry, (entry, dependencies)))
    |> Result.all
  in
  let* indexed =
    match Map.of_alist (module String) entries_with_dependencies with
    | `Ok indexed -> Ok indexed
    | `Duplicate_key duplicate ->
        let entry =
          List.find_exn entries ~f:(fun entry -> String.equal (name entry) duplicate)
        in
        Error
          (Report.error Type (at entry)
             ("Several imported interfaces name module " ^ duplicate))
  in
  let rec visit visiting (seen, ordered) module_name =
    if Set.mem seen module_name then Ok (seen, ordered)
    else
      match Map.find indexed module_name with
      | None -> Ok (seen, ordered)
      | Some (entry, dependencies) ->
          if List.mem visiting module_name ~equal:String.equal then
            Error
              (Report.error Type (at entry)
                 ("Cyclic imported interface dependencies: "
                 ^ String.concat ~sep:" -> " (List.rev (module_name :: visiting))))
          else
            let* seen, ordered =
              List.fold_result dependencies ~init:(seen, ordered)
                ~f:(visit (module_name :: visiting))
            in
            Ok (Set.add seen module_name, entry :: ordered)
  in
  let* _, ordered =
    List.fold_result entries
      ~init:(Set.empty (module String), [])
      ~f:(fun state entry -> visit [] state (name entry))
  in
  Ok (List.rev ordered)
