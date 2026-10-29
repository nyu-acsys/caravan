(** Types whose heap contents have a fixed, fully known layout. *)

open Base

let is_closed ~environment ~parameters ~at typ =
  let expanded typ =
    Signature_contract.compiler ~at (fun () ->
        Types.get_desc (Ctype.expand_head environment typ))
  in
  let declaration path =
    Signature_contract.compiler ~at (fun () -> Env.find_type path environment)
  in
  let rec depends_on_parameter (path : Path.t) =
    match path with
    | Pident id -> List.exists parameters ~f:(Ident.same id)
    | Pdot (parent, _) | Pextra_ty (parent, _) -> depends_on_parameter parent
    | Papply (fn, argument) -> depends_on_parameter fn || depends_on_parameter argument
  in
  let rec closed seen typ =
    match expanded typ with
    | Ok (Tconstr (path, [], _))
      when Path.same path Predef.path_int
           || Path.same path Predef.path_bool
           || Path.same path Predef.path_unit ->
        true
    | Ok (Tconstr (path, [ element ], _))
      when Path.same path Predef.path_list
           || Path.same path Predef.path_option
           || Datatypes.is_ref path || Datatypes.is_atomic path ->
        closed seen element
    | Ok (Tconstr (path, [], _)) ->
        if depends_on_parameter path then false
        else
          begin match declaration path with
          | Ok definition when List.is_empty definition.type_params ->
              if List.mem seen path ~equal:Path.same then true
              else
                let seen = path :: seen in
                begin match definition.type_kind with
                | Type_variant (constructors, _) ->
                    List.for_all constructors ~f:(fun constructor ->
                        match constructor.Types.cd_args with
                        | Cstr_tuple arguments -> List.for_all arguments ~f:(closed seen)
                        | Cstr_record _ -> false)
                | Type_record (fields, _) ->
                    List.for_all fields ~f:(fun field -> closed seen field.Types.ld_type)
                | Type_abstract _ | Type_open | Type_external _ -> false
                end
          | Ok _ | Error _ -> false
          end
    | Ok (Ttuple elements) ->
        List.for_all elements ~f:(fun (_, element) -> closed seen element)
    | Ok (Tpoly (element, [])) -> closed seen element
    | Ok _ | Error _ -> false
  in
  closed [] typ
