(** Nominal operation views; source type and resource identities remain in the inventory.
*)

open Base

type t = {
  binding : Module_inventory.checked_binding;
  name : string;
  interface : string;
  target : string option;
  members : (string * string) list;
  grouped : bool;
}

type schema = { interface : string; members : (string * string) list }

let plan ?(schema = fun _ -> None) bindings =
  let same_context (left : Module_inventory.checked_binding) right =
    (* The shared schema and immutable substitution snapshot retain lexical captures. *)
    phys_equal left.expected right.Module_inventory.expected
    && phys_equal left.parameter_substitution right.parameter_substitution
  in
  let add previous (binding : Module_inventory.checked_binding) =
    let base = String.uncapitalize (String.concat ~sep:"_" binding.namespace) in
    let name = Fresh_names.fresh ("Checked_" ^ base) in
    let requested = schema binding in
    let known =
      List.find previous ~f:(fun (view : t) ->
          (match requested with
            | Some schema -> String.equal schema.interface view.interface
            | None -> same_context view.binding binding)
          && (Path.same view.binding.actual_path binding.actual_path
             || List.mem view.binding.paths binding.actual_path ~equal:Path.same))
    in
    let view =
      match known with
      | Some view ->
          {
            binding;
            name;
            interface = view.interface;
            target = Some (Option.value view.target ~default:view.name);
            members = view.members;
            grouped = false;
          }
      | None ->
          {
            binding;
            name;
            interface =
              Option.value_map requested
                ~default:(Fresh_names.fresh ("Checked_contract_" ^ base))
                ~f:(fun schema -> schema.interface);
            target = None;
            members =
              (match requested with
              | Some schema -> schema.members
              | None ->
                  List.map binding.expected.signature_values ~f:(fun (member, _) ->
                      (member, Fresh_names.fresh ("checked_" ^ base ^ "_" ^ member))));
            grouped = Option.is_some requested;
          }
    in
    view :: previous
  in
  let bindings =
    List.filter bindings ~f:(fun (binding : Module_inventory.checked_binding) ->
        (not (List.is_empty binding.expected.signature_values))
        || Option.is_some (schema binding))
  in
  let views = List.rev (List.fold bindings ~init:[] ~f:add) in
  let targets =
    Set.of_list (module String) (List.filter_map views ~f:(fun view -> view.target))
  in
  List.map views ~f:(fun view ->
      {
        view with
        grouped = view.grouped || Option.is_some view.target || Set.mem targets view.name;
      })
