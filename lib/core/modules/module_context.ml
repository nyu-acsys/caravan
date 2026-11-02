(** Translation contexts for static modules and generic workers. *)

open Base
module S = Caravan_spec.Spec_ast

let ( let* ) = Result.( >>= )

type destination =
  | Flat
  | Worker of Generic_modules.t
  | Function_worker of Polymorphic_functions.t * destination
  | Proof_worker of Generic_parameters.t * destination

type t = {
  scope : Proof_scopes.scope;
  identity : Path.t option;
  parameters : Generic_proofs.parameter list;
  projection : Subst.t;
  namespace : string list;
  worker : Generic_proofs.t option;
  destination : destination;
}

type registry = { root : t; contexts : t list; scopes : Proof_scopes.t }

let collect_scopes (scopes : Proof_scopes.t) =
  let has_body (expression : Typedtree.module_expr) =
    let rec structural expression =
      match expression.Typedtree.mod_desc with
      | Tmod_structure _ -> true
      | Tmod_functor (_, inner) | Tmod_constraint (inner, _, _, _) -> structural inner
      | Tmod_ident _ | Tmod_apply _ | Tmod_apply_unit _ | Tmod_unpack _ -> false
    in
    structural expression
  in
  let rec collect parent =
    List.fold_result parent.Proof_scopes.structure.str_items ~init:[]
      ~f:(fun found item ->
        match item.Typedtree.str_desc with
        | Tstr_module
            { mb_id = Some id; mb_name = { txt = Some name; loc }; mb_expr; mb_loc; _ }
          when has_body mb_expr ->
            let* candidate =
              Proof_scopes.child_scope ~check_header:false parent (S.mk_id ~loc name) []
                mb_loc
            in
            let existing =
              List.find scopes.scopes ~f:(fun scope ->
                  Option.exists scope.Proof_scopes.declaration_id ~f:(Ident.same id))
            in
            let current = Option.value existing ~default:candidate in
            let found = if Option.is_some existing then found else candidate :: found in
            if List.is_empty current.parameters then
              let* children = collect current in
              Ok (children @ found)
            else Ok found
        | _ -> Ok found)
  in
  let* added = collect scopes.root in
  let ordered =
    List.stable_sort
      (scopes.scopes @ List.rev added)
      ~compare:(fun left right ->
        Int.compare left.source_location.loc_start.pos_cnum
          right.source_location.loc_start.pos_cnum)
  in
  Ok { scopes with scopes = ordered }

let plan ~scopes generic_plans =
  let context scope =
    if Option.is_some scope.Proof_scopes.definition then None
    else
      match Generic_proofs.owner generic_plans (Some scope) with
      | Some worker ->
          Some
            {
              scope;
              identity = scope.owner;
              parameters = worker.parameters;
              projection = Generic_proofs.projection worker;
              namespace = String.split worker.group.name ~on:'.';
              worker = Some worker;
              destination = Worker worker.group;
            }
      | None ->
          if Option.is_some (Proof_bindings.functor_ancestor scopes scope) then None
          else
            Some
              {
                scope;
                identity = scope.owner;
                parameters = [];
                projection = Subst.identity;
                namespace = [];
                worker = None;
                destination = Flat;
              }
  in
  let contexts = List.filter_map scopes.scopes ~f:context in
  let root =
    List.find_exn contexts ~f:(fun context ->
        Proof_scopes.same_scope context.scope scopes.root)
  in
  { root; contexts; scopes }

let find registry = function
  | None -> Some registry.root
  | Some scope ->
      let owner =
        if Option.is_some scope.Proof_scopes.definition then scope.parent else scope.owner
      in
      List.find registry.contexts ~f:(fun context ->
          Option.equal Path.same context.identity owner)

let for_scope registry scope = Option.value (find registry scope) ~default:registry.root

let find_owner registry owner =
  Option.bind (Proof_scopes.find_owner registry.scopes owner) ~f:(fun scope ->
      find registry (Some scope))

let for_owner registry owner =
  Option.value (find_owner registry owner) ~default:registry.root

let for_location registry location =
  List.filter registry.scopes.scopes ~f:(fun scope ->
      Proof_bindings.contains scope.Proof_scopes.source_location location)
  |> List.max_elt ~compare:(fun left right ->
      Int.compare (List.length left.Proof_scopes.namespace) (List.length right.namespace))
  |> for_scope registry

let for_group registry group =
  List.find registry.contexts ~f:(fun context ->
      match context.destination with
      | Worker actual -> phys_equal actual group
      | Flat | Function_worker _ | Proof_worker _ -> false)

let member context backend = String.concat ~sep:"." (context.namespace @ [ backend ])

let contains context (binding : Proof_bindings.binding) =
  match context.worker with
  | Some worker -> Generic_proofs.contains worker binding
  | None -> Option.equal Path.same context.identity binding.entry.scope.owner

let project_type context typ =
  match context.worker with
  | Some _ -> Subst.type_expr context.projection typ
  | None -> typ

let parameter_pairs context =
  Option.value_map context.worker ~default:[] ~f:Generic_proofs.parameter_pairs

let runtime_pairs context =
  Option.value_map context.worker ~default:[] ~f:(fun worker ->
      List.filter_map (Generic_proofs.runtime_types worker) ~f:(fun original ->
          Option.map
            (Generic_proofs.matching_type original
               worker.group.representative.declarations) ~f:(fun target ->
              (original, target))
          |> Option.filter ~f:(fun (_, target) ->
              not (Ident.same original.typ_id target.Typedtree.typ_id))))

let rec same_destination left right =
  match (left, right) with
  | Flat, Flat -> true
  | Worker left, Worker right -> phys_equal left right
  | Function_worker (left, left_parent), Function_worker (right, right_parent) ->
      Ident.same left.id right.id
      && String.equal left.name right.name
      && same_destination left_parent right_parent
  | Proof_worker (left, left_parent), Proof_worker (right, right_parent) ->
      String.equal left.key right.key
      && String.equal left.name right.name
      && same_destination left_parent right_parent
  | (Flat | Worker _ | Function_worker _ | Proof_worker _), _ -> false

let is_function = function
  | Function_worker _ -> true
  | Flat | Worker _ | Proof_worker _ -> false

let emits_owner registry ~destination owner =
  same_destination (for_owner registry owner).destination destination

let rec groups = function
  | Flat -> []
  | Worker group -> [ group ]
  | Function_worker (_, parent) -> groups parent
  | Proof_worker (_, parent) -> groups parent

let namespace = function
  | Flat -> []
  | Worker group -> String.split group.name ~on:'.'
  | Function_worker (worker, _) -> String.split worker.name ~on:'.'
  | Proof_worker (worker, _) -> String.split worker.name ~on:'.'

let local_name destination backend =
  match namespace destination with
  | [] -> backend
  | namespace ->
      Option.value
        (String.chop_prefix backend ~prefix:(String.concat ~sep:"." namespace ^ "."))
        ~default:backend
