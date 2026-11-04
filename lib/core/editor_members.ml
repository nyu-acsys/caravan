(** Source declarations and the complete backend checks attributed to them. *)

open Base
module R = Raven_api
module S = Caravan_spec.Spec_ast

type status =
  | Unchecked
  | Checked
  | Trusted
  | Verified
  | Pending
  | Skipped
  | Timeout
  | Failed

type member = {
  id : string;
  name : string;
  kind : string;
  name_loc : Location.t;
  extent : Location.t;
  parent : string option;
  group : bool;
  trusted : bool;
  ranges : Location.t list;
  own_status : status;
  status : status;
  cached : bool;
  checks : R.Progress.check list;
  counts : (status * int) list;
}

let status_to_string = function
  | Unchecked -> "unchecked"
  | Checked -> "checked"
  | Trusted -> "trusted"
  | Verified -> "verified"
  | Pending -> "pending"
  | Skipped -> "skipped"
  | Timeout -> "timeout"
  | Failed -> "failed"

let identity ~kind (at : Location.t) =
  Printf.sprintf "%s:%d:%d:%s" at.loc_start.pos_fname at.loc_start.pos_cnum
    at.loc_end.pos_cnum kind

let make ?parent ?(group = false) ?(trusted = false) ?ranges ~name ~kind ~name_loc ~extent
    () =
  let status = if trusted then Trusted else Unchecked in
  {
    id = identity ~kind name_loc;
    name;
    kind;
    name_loc;
    extent;
    parent;
    group;
    trusted;
    ranges = Option.value ranges ~default:[ extent ];
    own_status = status;
    status;
    cached = false;
    checks = [];
    counts = [];
  }

let size (at : Location.t) = at.loc_end.pos_cnum - at.loc_start.pos_cnum
let contains = Declaration_scope.contains

let unique_innermost members at =
  let candidates =
    List.filter_map members ~f:(fun member ->
        List.filter member.ranges ~f:(fun range -> contains range at)
        |> List.map ~f:size
        |> List.min_elt ~compare:Int.compare
        |> Option.map ~f:(fun size -> (member, size)))
  in
  match List.min_elt candidates ~compare:(fun (_, a) (_, b) -> Int.compare a b) with
  | None -> None
  | Some (_, size) ->
      begin match List.filter candidates ~f:(fun (_, other) -> size = other) with
      | [ (member, _) ] -> Some member
      | _ -> None
      end

let merge_extent (at : Location.t) (locations : Location.t list) =
  List.fold locations ~init:at ~f:(fun (extent : Location.t) (at : Location.t) ->
      if String.equal extent.loc_start.pos_fname at.loc_start.pos_fname then
        {
          extent with
          loc_start =
            (if at.loc_start.pos_cnum < extent.loc_start.pos_cnum then at.loc_start
             else extent.loc_start);
          loc_end =
            (if at.loc_end.pos_cnum > extent.loc_end.pos_cnum then at.loc_end
             else extent.loc_end);
        }
      else extent)

let declaration_shape declaration =
  let term (t : S.term) = t.term_loc in
  match declaration with
  | S.Proof_module { module_loc; _ } | Proof_definition { module_loc; _ } ->
      ("proof_module", true, [ module_loc ])
  | Proof_predicate p ->
      ("predicate", false, List.map (Option.to_list p.pred_body) ~f:term)
  | Proof_lemma { lemma_requires; lemma_ensures; lemma_variant; lemma_body; _ } ->
      ( "lemma",
        false,
        lemma_body.proof_loc
        :: List.map (lemma_requires @ lemma_ensures @ lemma_variant) ~f:term )
  | Proof_function { function_body; _ } -> ("function", false, [ term function_body ])
  | Proof_invariant { inv_body; _ } -> ("invariant", false, [ term inv_body ])
  | Proof_view { view_value; _ } -> ("view", false, [ term view_value ])
  | Proof_action { action_consumes; action_update; action_helps; _ } ->
      ( "action",
        false,
        List.map
          (Option.to_list action_consumes
          @ List.map action_update ~f:snd
          @ Option.value_map action_helps ~default:[] ~f:(fun (a, b, c) -> [ a; b; c ]))
          ~f:term )
  | Proof_type _ -> ("type", false, [])
  | Proof_resource _ -> ("resource", false, [])
  | Proof_au _ -> ("atomic_update", false, [])
  | Proof_field _ -> ("field", false, [])
  | Proof_state _ -> ("state", false, [])

let runtime_modules ~parent typed =
  let rec is_functor (expression : Typedtree.module_expr) =
    match expression.mod_desc with
    | Tmod_functor _ -> true
    | Tmod_constraint (body, _, _, _) -> is_functor body
    | _ -> false
  in
  let rec structure parent namespace (body : Typedtree.structure) =
    List.concat_map body.str_items ~f:(fun item ->
        match item.Typedtree.str_desc with
        | Tstr_module binding -> module_binding parent namespace binding
        | Tstr_recmodule bindings ->
            List.concat_map bindings ~f:(module_binding parent namespace)
        | _ -> [])
  and module_binding parent namespace (binding : Typedtree.module_binding) =
    match binding.mb_name.txt with
    | None -> module_body parent namespace binding.mb_expr
    | Some name ->
        let namespace = namespace @ [ name ] in
        let member =
          make ~parent
            ~name:(String.concat ~sep:"." namespace)
            ~kind:(if is_functor binding.mb_expr then "functor" else "module")
            ~name_loc:binding.mb_name.loc ~extent:binding.mb_loc ~group:true ()
        in
        (binding.mb_id, member) :: module_body member.id namespace binding.mb_expr
  and module_body parent namespace (body : Typedtree.module_expr) =
    match body.mod_desc with
    | Tmod_structure body -> structure parent namespace body
    | Tmod_functor (_, body) | Tmod_constraint (body, _, _, _) ->
        module_body parent namespace body
    | _ -> []
  in
  structure parent [] typed

let runtime_module_for_scope bindings (scope : Proof_scopes.scope) =
  let by_identity =
    Option.bind scope.declaration_id ~f:(fun declaration ->
        List.find_map bindings ~f:(fun (id, member) ->
            Option.some_if (Option.exists id ~f:(Ident.same declaration)) member))
  in
  Option.first_some by_identity
    (List.find_map bindings ~f:(fun (_, member) ->
         Option.some_if
           (Declaration_scope.same_place member.extent scope.source_location)
           member))

let collect (scopes : Program_scopes.t) =
  let source = scopes.source in
  let root =
    make ~name:source.file ~kind:"file" ~name_loc:source.scope.location
      ~extent:source.scope.location ~group:true ()
  in
  let module_bindings = runtime_modules ~parent:root.id source.typed in
  let modules = List.map module_bindings ~f:snd in
  let module_parent at =
    Option.value_map (unique_innermost modules at) ~default:root.id ~f:(fun m -> m.id)
  in
  let functions =
    List.map scopes.funcs ~f:(fun (func : Procedures.func) ->
        let contract_ranges =
          Option.value_map func.contract_origin ~default:[]
            ~f:(fun (annotation : Annotation.t) ->
              annotation.Annotation.loc
              :: Option.to_list
                   (Option.map annotation.origin ~f:(fun (origin : Annotation.origin) ->
                        origin.loc)))
        in
        let parent = module_parent func.loc in
        let name =
          match List.find modules ~f:(fun member -> String.equal member.id parent) with
          | Some owner -> owner.name ^ "." ^ Ident.name func.id
          | None -> Ident.name func.id
        in
        make ~parent ~name ~kind:"function" ~name_loc:func.name_loc ~extent:func.loc
          ~trusted:func.trusted ~ranges:(func.loc :: contract_ranges) ())
    |> List.dedup_and_sort ~compare:(fun a b -> String.compare a.id b.id)
  in
  let functions =
    List.map functions ~f:(fun member ->
        let outer =
          List.filter functions ~f:(fun candidate ->
              (not (String.equal candidate.id member.id))
              && contains candidate.extent member.extent)
        in
        let parent =
          Option.value_map (unique_innermost outer member.extent) ~default:member.parent
            ~f:(fun outer -> Some outer.id)
        in
        { member with parent })
  in
  let functions =
    List.fold source.outline_annotations ~init:functions
      ~f:(fun functions (annotation : Annotation.t) ->
        match
          (annotation.Annotation.origin, unique_innermost functions annotation.loc)
        with
        | Some origin, Some owner ->
            List.map functions ~f:(fun member ->
                if String.equal member.id owner.id then
                  { member with ranges = origin.loc :: member.ranges }
                else member)
        | _ -> functions)
  in
  let rec proof parent namespace declarations =
    List.concat_map declarations ~f:(fun declaration ->
        let name = Proof_scopes.name declaration in
        let kind, group, locations = declaration_shape declaration in
        let extent = merge_extent name.pid_loc locations in
        let qualified = namespace @ [ name.pid_str ] in
        let parent =
          if group then
            match Proof_scopes.find_namespace source.proof_scopes qualified with
            | Some scope ->
                Option.value_map (runtime_module_for_scope module_bindings scope)
                  ~default:parent ~f:(fun member -> member.id)
            | None -> parent
          else parent
        in
        let member =
          make ~parent
            ~name:(String.concat ~sep:"." qualified)
            ~kind ~name_loc:name.pid_loc ~extent ~group ()
        in
        member
        ::
        (match declaration with
        | S.Proof_module { module_declarations; _ }
        | Proof_definition { module_declarations; _ } ->
            proof member.id qualified module_declarations
        | _ -> []))
  in
  let annotation_predicates ~interface annotations =
    List.filter_map annotations ~f:(fun (annotation : Annotation.t) ->
        if not (Annotation.predicate_declaration ~interface annotation) then None
        else
          match Annotation.predicate annotation with
          | Error _ -> None
          | Ok predicate ->
              Some
                (make
                   ~parent:(module_parent annotation.loc)
                   ~name:predicate.pred_name.pid_str
                   ~kind:(if predicate.pred_persistent then "invariant" else "predicate")
                   ~name_loc:predicate.pred_name.pid_loc ~extent:annotation.loc ()))
  in
  let predicates =
    annotation_predicates ~interface:false scopes.annotations
    @ Option.value_map source.interface ~default:[]
        ~f:(fun (interface : Source.interface) ->
          annotation_predicates ~interface:true
            (Annotation.of_comments interface.interface_comments))
  in
  (root :: modules) @ functions @ proof root.id [] source.proof @ predicates

let outcome_status (outcome : R.Progress.outcome) : status =
  match outcome with
  | R.Progress.Cached | Verified -> Verified
  | Pending -> Pending
  | Timeout -> Timeout
  | Failed -> Failed

let rank = function
  | Unchecked | Checked | Trusted -> 0
  | Verified -> 1
  | Pending -> 2
  | Skipped -> 3
  | Timeout -> 4
  | Failed -> 5

let worst statuses =
  List.max_elt statuses ~compare:(fun a b -> Int.compare (rank a) (rank b))

let check_location (check : R.Progress.check) =
  {
    Location.loc_start = R.Loc.start check.loc;
    loc_end = R.Loc.stop check.loc;
    loc_ghost = false;
  }

let same_check (a : R.Progress.check) (b : R.Progress.check) =
  String.equal a.name b.name
  && Declaration_scope.same_place (check_location a) (check_location b)

let dedup_checks (checks : R.Progress.check list) =
  let outcome_rank = function
    | R.Progress.Cached -> 0
    | outcome -> 1 + rank (outcome_status outcome)
  in
  List.fold checks ~init:[] ~f:(fun checks (check : R.Progress.check) ->
      match List.find checks ~f:(same_check check) with
      | None -> check :: checks
      | Some previous ->
          let selected =
            if outcome_rank check.outcome > outcome_rank previous.outcome then check
            else previous
          in
          List.map checks ~f:(fun other ->
              if same_check check other then selected else other))
  |> List.rev

let summarize members =
  let gate =
    List.find members ~f:(fun member -> String.equal member.kind "file")
    |> Option.bind ~f:(fun root ->
        match root.own_status with
        | Pending | Skipped | Timeout | Failed -> Some root.own_status
        | Unchecked | Checked | Trusted | Verified -> None)
  in
  let rec descendants seen parent =
    List.concat_map members ~f:(fun member ->
        if
          Option.equal String.equal member.parent (Some parent)
          && not (List.mem seen member.id ~equal:String.equal)
        then member :: descendants (member.id :: seen) member.id
        else [])
  in
  List.map members ~f:(fun member ->
      let children = descendants [ member.id ] member.id in
      let status =
        worst
          ((if member.group then Option.to_list gate else [])
          @ (member.own_status :: List.map children ~f:(fun child -> child.own_status)))
        |> Option.value ~default:member.own_status
      in
      let counted =
        if member.group then List.filter children ~f:(fun child -> not child.group)
        else [ member ]
      in
      let counts =
        List.fold counted ~init:[] ~f:(fun counts child ->
            let count =
              List.Assoc.find counts child.own_status ~equal:Poly.equal
              |> Option.value ~default:0
            in
            List.Assoc.add counts child.own_status (count + 1) ~equal:Poly.equal)
      in
      let checks =
        member.checks @ List.concat_map children ~f:(fun child -> child.checks)
      in
      let cached =
        Poly.equal status Verified
        && (not (List.is_empty checks))
        && List.for_all checks ~f:(fun check ->
            Poly.equal check.outcome R.Progress.Cached)
      in
      { member with status; cached; counts })

let project inventory (progress : R.Progress.t) =
  let root = List.find inventory ~f:(fun member -> String.equal member.kind "file") in
  let attributed =
    List.filter_map (dedup_checks progress.checks) ~f:(fun check ->
        let owner = unique_innermost inventory (check_location check) in
        Option.map (Option.first_some owner root) ~f:(fun owner -> (owner.id, check)))
  in
  List.map inventory ~f:(fun member ->
      let checks =
        List.filter_map attributed ~f:(fun (owner, check) ->
            Option.some_if (String.equal owner member.id) check)
      in
      let own_status =
        match worst (List.map checks ~f:(fun check -> outcome_status check.outcome)) with
        | Some status -> status
        | None -> if member.trusted then Trusted else Checked
      in
      { member with checks; own_status; status = own_status })
  |> summarize

let finish ~verified members =
  let attributed_failure =
    List.exists members ~f:(fun member ->
        match member.own_status with Failed | Timeout -> true | _ -> false)
  in
  List.map members ~f:(fun member ->
      let own_status =
        match member.own_status with
        | Pending -> Skipped
        | Unchecked when verified -> Checked
        | other -> other
      in
      let own_status =
        if
          (not verified) && (not attributed_failure)
          && String.equal member.kind "file"
          && rank own_status < rank Skipped
        then Skipped
        else own_status
      in
      { member with own_status; status = own_status })
  |> summarize
