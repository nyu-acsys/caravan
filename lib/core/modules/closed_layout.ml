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
    | Ok (Tvar _) when Types.get_level typ = Btype.generic_level ->
        (* Generalized values use the enclosing function worker's dictionary. *)
        true
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
    | Ok (Tconstr (path, arguments, _)) ->
        if depends_on_parameter path then false
        else
          begin match declaration path with
          (* A locally abstract type, as a generalized variable, uses the function
             worker's dictionary. *)
          | Ok { type_is_newtype = true; _ } -> true
          | Ok definition when List.length definition.type_params = List.length arguments
            ->
              let substitutions = List.zip_exn definition.type_params arguments in
              let rec substitute typ =
                match List.Assoc.find substitutions typ ~equal:Types.eq_type with
                | Some actual -> actual
                | None ->
                    begin match Types.get_desc typ with
                    | Tvar _ | Tunivar _ -> typ
                    | desc -> Ctype.newty (Btype.copy_type_desc substitute desc)
                    end
              in
              if not (List.for_all arguments ~f:(closed seen)) then false
              else if List.mem seen path ~equal:Path.same then true
              else
                let seen = path :: seen in
                begin match definition.type_kind with
                | Type_variant (constructors, _) ->
                    List.for_all constructors ~f:(fun constructor ->
                        match constructor.Types.cd_args with
                        | Cstr_tuple arguments ->
                            List.for_all arguments ~f:(fun typ ->
                                closed seen (substitute typ))
                        | Cstr_record _ -> false)
                | Type_record (fields, _) ->
                    List.for_all fields ~f:(fun field ->
                        (List.is_empty arguments
                        || Poly.equal field.Types.ld_mutable Asttypes.Immutable)
                        && closed seen (substitute field.ld_type))
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
