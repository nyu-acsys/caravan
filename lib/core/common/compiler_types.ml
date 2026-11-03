(** Compiler-only type identities and their source-facing diagnostic names. *)

open Base

(** Project related types together so shared generic variables retain their identity. *)
let map_group types ~f =
  match types with
  | [] -> []
  | [ typ ] -> [ f typ ]
  | types -> (
      let packed =
        Btype.newgenty (Types.Ttuple (List.map types ~f:(fun typ -> (None, typ))))
      in
      match Types.get_desc (f packed) with
      | Ttuple fields -> List.map fields ~f:snd
      | _ -> failwith "A type projection must preserve tuple structure")

(** Fresh generic structure lets compiler instantiation reach quantified variables. *)
let rec scheme_structure typ =
  match Types.get_desc typ with
  | Tvar _ | Tunivar _ -> typ
  | desc -> Btype.newgenty (Btype.copy_type_desc scheme_structure desc)

let prefix = "$caravan_"

let internal_name ~(at : Location.t) member =
  prefix ^ Int.to_string at.loc_start.pos_cnum ^ "_" ^ member

let internal_path = function
  | Path.Pident id -> String.is_prefix (Ident.name id) ~prefix
  | Pdot _ | Papply _ | Pextra_ty _ -> false

let projection environment =
  let rec signature parent (seen, substitution) members =
    List.fold members ~init:(seen, substitution) ~f:(fun state -> function
      | Types.Sig_type (id, { type_manifest = Some typ; _ }, _, _) ->
          begin match Types.get_desc typ with
          | Tconstr (Path.Pident hidden, [], _) when internal_path (Pident hidden) ->
              let seen, substitution = state in
              if List.mem seen hidden ~equal:Ident.same then state
              else
                ( hidden :: seen,
                  Subst.add_type hidden (Path.Pdot (parent, Ident.name id)) substitution
                )
          | _ -> state
          end
      | Sig_module (id, _, { md_type = Mty_signature members; _ }, _, _) ->
          signature (Path.Pdot (parent, Ident.name id)) state members
      | _ -> state)
  in
  let rec summary state = function
    | Env.Env_empty -> snd state
    | Env_module (previous, id, _, { md_type = Mty_signature members; _ }) ->
        let visible =
          try
            let path, _ =
              Env.find_module_by_name (Longident.Lident (Ident.name id)) environment
            in
            Path.same path (Path.Pident id)
          with Stdlib.Not_found -> false
        in
        let state = if visible then signature (Pident id) state members else state in
        summary state previous
    | Env_value (previous, _, _)
    | Env_type (previous, _, _)
    | Env_extension (previous, _, _)
    | Env_module (previous, _, _, _)
    | Env_modtype (previous, _, _)
    | Env_class (previous, _, _)
    | Env_cltype (previous, _, _)
    | Env_open (previous, _)
    | Env_not_aliasable (previous, _)
    | Env_constraints (previous, _)
    | Env_copy_types previous
    | Env_persistent (previous, _)
    | Env_value_unbound (previous, _, _)
    | Env_module_unbound (previous, _, _) ->
        summary state previous
  in
  summary ([], Subst.identity) (Env.summary environment)

let contains_internal typ =
  let rec contains seen typ =
    let id = Types.get_id typ in
    if List.mem seen id ~equal:Int.equal then false
    else
      let seen = id :: seen in
      match Types.get_desc typ with
      | Tconstr (path, arguments, _) ->
          internal_path path || List.exists arguments ~f:(contains seen)
      | Tarrow (_, argument, result, _) -> contains seen argument || contains seen result
      | Ttuple elements -> List.exists elements ~f:(fun (_, typ) -> contains seen typ)
      | Tpoly (body, _) -> contains seen body
      | _ -> false
  in
  contains [] typ

let diagnostic_exception = function
  | Typecore.Error (at, environment, error) ->
      let substitution = projection environment in
      let trace (error : Errortrace.unification_error) =
        let expanded (expansion : Errortrace.expanded_type) =
          if not (contains_internal expansion.ty || contains_internal expansion.expanded)
          then expansion
          else
            let project typ =
              if contains_internal typ then Subst.type_expr substitution typ else typ
            in
            let ty = project expansion.ty in
            let expanded =
              match Types.get_desc expansion.expanded with
              | Tconstr (path, _, _) when internal_path path -> ty
              | _ -> project expansion.expanded
            in
            { Errortrace.ty; expanded }
        in
        Errortrace.unification_error ~trace:(Errortrace.map expanded error.trace)
      in
      let error =
        match error with
        | Expr_type_clash (error, context, expression) ->
            Typecore.Expr_type_clash (trace error, context, expression)
        | Pattern_type_clash (error, pattern) -> Pattern_type_clash (trace error, pattern)
        | Label_mismatch (label, error) -> Label_mismatch (label, trace error)
        | Or_pattern_type_clash (id, error) -> Or_pattern_type_clash (id, trace error)
        | Function_arity_type_clash details ->
            Function_arity_type_clash { details with trace = trace details.trace }
        | error -> error
      in
      Typecore.Error (at, environment, error)
  | exception_ -> exception_
