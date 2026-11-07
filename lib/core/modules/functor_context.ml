(** Source functor applications and their accumulated parameter bindings. *)

open Base
open Typedtree

type stage = {
  parameter : Typedtree.functor_parameter;
  argument : Path.t option;
  identity : Path.t;
  location : Location.t;
}

type application = {
  scope : Proof_scopes.scope;
  stages : stage list;
  bindings : (Ident.t * Path.t) list;
  chain : (string * Ident.t) list;
  result : Path.t;
  applicative_identity : Path.t;
  location : Location.t;
  sealed : bool;
}

type partial = {
  scope : Proof_scopes.scope;
  stages : stage list;
  identity : Path.t;
  sealed : bool;
}

let find_at applications location =
  List.find applications ~f:(fun application ->
      Declaration_scope.same_place application.location location)

let find_result applications result =
  List.find applications ~f:(fun application -> Path.same application.result result)

let result_paths application =
  let local =
    Option.map (List.last application.chain) ~f:(fun (_, id) -> Path.Pident id)
  in
  List.dedup_and_sort (application.result :: Option.to_list local) ~compare:Path.compare

let find_stage_at applications location =
  List.find_map applications ~f:(fun application ->
      List.find application.stages ~f:(fun stage ->
          Declaration_scope.same_place stage.location location))

let same_scope left right =
  Option.equal Path.same left.Proof_scopes.owner right.Proof_scopes.owner

let named_parameters scope =
  List.filter_map scope.Proof_scopes.parameters ~f:(function
    | Typedtree.Named (Some id, _, _) -> Some id
    | Unit | Named (None, _, _) -> None)

let substitution application =
  List.fold application.bindings ~init:Subst.identity ~f:(fun substitution (id, path) ->
      Subst.add_module id path substitution)

let complete partial =
  Int.equal (List.length partial.stages) (List.length partial.scope.parameters)

let bindings partial =
  List.filter_map partial.stages ~f:(fun stage ->
      match (stage.parameter, stage.argument) with
      | Typedtree.Named (Some id, _, _), Some path -> Some (id, path)
      | Unit, None | Named _, None | Unit, Some _ | Named (None, _, _), Some _ -> None)

let collect (scopes : Proof_scopes.t) =
  let rec path (expression : Typedtree.module_expr) =
    match expression.mod_desc with
    | Tmod_ident (path, _) -> Some path
    | Tmod_constraint (body, _, Tmodtype_implicit, _) -> path body
    | Tmod_structure _ | Tmod_functor _ | Tmod_apply _ | Tmod_apply_unit _ | Tmod_unpack _
    | Tmod_constraint (_, _, Tmodtype_explicit _, _) ->
        None
  in
  let find_scope path =
    List.find scopes.scopes ~f:(fun scope ->
        Option.exists scope.owner ~f:(Path.same path)
        || Option.exists scope.declaration_id ~f:(fun id ->
            Path.same path (Path.Pident id)))
  in
  let rec expression registry ~result (value : Typedtree.module_expr) =
    match value.mod_desc with
    | Tmod_constraint (body, _, Tmodtype_implicit, _) -> expression registry ~result body
    | Tmod_constraint (body, _, Tmodtype_explicit _, _) ->
        Option.map (expression registry ~result body) ~f:(fun partial ->
            { partial with sealed = true })
    | Tmod_ident (name, _) ->
        Option.first_some
          (List.Assoc.find registry name ~equal:Path.same)
          (Option.map (find_scope name) ~f:(fun scope ->
               { scope; stages = []; identity = name; sealed = false }))
    | Tmod_apply (callee, argument, _) ->
        Option.bind (expression registry ~result:None callee) ~f:(fun partial ->
            Option.bind (path argument) ~f:(fun argument ->
                let argument = Env.normalize_module_path None value.mod_env argument in
                append partial (Some argument) ~result value.mod_loc))
    | Tmod_apply_unit callee ->
        Option.bind (expression registry ~result:None callee) ~f:(fun partial ->
            append partial None ~result value.mod_loc)
    | Tmod_structure _ | Tmod_functor _ | Tmod_unpack _ -> None
  and append partial argument ~result location =
    let index = List.length partial.stages in
    match List.nth partial.scope.parameters index with
    | None -> None
    | Some parameter ->
        let identity =
          match (parameter, argument) with
          | Typedtree.Named _, Some argument -> Path.Papply (partial.identity, argument)
          | Unit, None ->
              Option.value_or_thunk result ~default:(fun () ->
                  Path.Pident (Ident.create_local "functor_stage"))
          | Named _, None | Unit, Some _ -> partial.identity
        in
        begin match (parameter, argument) with
        | Named _, Some _ | Unit, None ->
            Some
              {
                partial with
                stages = partial.stages @ [ { parameter; argument; identity; location } ];
                identity;
              }
        | Named _, None | Unit, Some _ -> None
        end
  in
  let rec structure registry parent chain (body : Typedtree.structure) =
    List.fold body.str_items ~init:(registry, []) ~f:(fun (registry, found) item ->
        match item.str_desc with
        | Tstr_module { mb_id = Some id; mb_name = { txt = Some name; _ }; mb_expr; _ } ->
            let result =
              Option.value_map parent ~default:(Path.Pident id) ~f:(fun parent ->
                  Path.Pdot (parent, name))
            in
            let chain = chain @ [ (name, id) ] in
            let partial = expression registry ~result:(Some result) mb_expr in
            let registry =
              Option.value_map partial ~default:registry ~f:(fun partial ->
                  (Path.Pident id, partial) :: (result, partial) :: registry)
            in
            let applied =
              let rec applied expression =
                match expression.Typedtree.mod_desc with
                | Tmod_apply _ | Tmod_apply_unit _ -> true
                | Tmod_constraint (inner, _, _, _) -> applied inner
                | Tmod_ident _ | Tmod_structure _ | Tmod_functor _ | Tmod_unpack _ ->
                    false
              in
              applied mb_expr
            in
            let own =
              Option.to_list
                (Option.bind partial ~f:(fun partial ->
                     if applied && complete partial then
                       Option.map (List.last partial.stages) ~f:(fun last ->
                           {
                             scope = partial.scope;
                             stages = partial.stages;
                             bindings = bindings partial;
                             chain;
                             result;
                             applicative_identity = partial.identity;
                             location = last.location;
                             sealed = partial.sealed;
                           })
                     else None))
            in
            let rec nested (value : Typedtree.module_expr) =
              match value.mod_desc with
              | Tmod_structure body -> structure registry (Some result) chain body
              | Tmod_constraint (body, _, _, _) -> nested body
              | Tmod_ident _ | Tmod_functor _ | Tmod_apply _ | Tmod_apply_unit _
              | Tmod_unpack _ ->
                  (registry, [])
            in
            let registry, nested = nested mb_expr in
            (registry, found @ own @ nested)
        | _ -> (registry, found))
  in
  snd (structure [] None [] scopes.root.structure)
