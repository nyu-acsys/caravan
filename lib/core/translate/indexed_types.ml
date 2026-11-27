(** Source GADT indices, independently of their runtime representation. *)

open Base

let ( let* ) = Result.( >>= )

type role = Parameter | Value_index | Constructor_index

type t = {
  roles : role list;
  indices : bool list;
  results : (string * Types.type_expr list) list;
  labels : (string * (int * string) list) list;
  constant : bool;
}

let parameters metadata values =
  List.filter_map (List.zip_exn metadata.roles values) ~f:(fun (role, value) ->
      match role with Parameter -> Some value | Value_index | Constructor_index -> None)

let row_tags ~required typ =
  match Types.get_desc typ with
  | Tvariant row ->
      let* tags =
        List.fold_result (Types.row_fields row) ~init:[] ~f:(fun tags (name, field) ->
            match Types.row_field_repr field with
            | Rpresent None -> Ok (name :: tags)
            | Reither (true, [], _) -> Ok (if required then tags else name :: tags)
            | Rabsent -> Ok tags
            | Rpresent (Some _) | Reither _ -> Error ())
      in
      Ok (Types.row_closed row, List.sort tags ~compare:String.compare)
  | _ -> Error ()

let classify parameters results =
  let variable typ = match Types.get_desc typ with Tvar _ -> true | _ -> false in
  let _, reversed =
    List.foldi parameters ~init:([], []) ~f:(fun position (earlier, roles) _ ->
        let ordinary =
          List.for_all results ~f:(fun arguments ->
              let argument = List.nth_exn arguments position in
              variable argument
              && List.for_all earlier ~f:(fun other ->
                  not (Types.eq_type argument (List.nth_exn arguments other))))
        in
        if ordinary then (position :: earlier, Parameter :: roles)
        else
          let row =
            List.for_all results ~f:(fun arguments ->
                Result.is_ok (row_tags ~required:true (List.nth_exn arguments position)))
          in
          (earlier, (if row then Constructor_index else Value_index) :: roles))
  in
  List.rev reversed

let compiler_roles (declaration : Types.type_declaration) =
  match declaration.type_kind with
  | Type_variant (constructors, _) ->
      let results =
        List.map constructors ~f:(fun constructor ->
            match Option.map constructor.Types.cd_res ~f:Types.get_desc with
            | Some (Tconstr (_, arguments, _)) -> arguments
            | Some _ | None -> declaration.type_params)
      in
      classify declaration.type_params results
  | _ -> List.map declaration.type_params ~f:(fun _ -> Parameter)

let analyze (declaration : Typedtree.type_declaration) constructors =
  let unsupported at = Report.unsupported at "This GADT index or existential payload" in
  let* results =
    Result.all
      (List.map constructors ~f:(fun (constructor : Typedtree.constructor_declaration) ->
           let result =
             Option.value_map constructor.cd_res
               ~default:
                 (Ctype.newconstr (Path.Pident declaration.typ_id)
                    declaration.typ_type.type_params) ~f:(fun result ->
                 result.Typedtree.ctyp_type)
           in
           match Types.get_desc result with
           | Tconstr (_, arguments, _) -> Ok (constructor, arguments)
           | _ -> unsupported constructor.cd_loc))
  in
  let roles = classify declaration.typ_params (List.map results ~f:snd) in
  let constant =
    List.for_all constructors ~f:(fun constructor ->
        match constructor.Typedtree.cd_args with Cstr_tuple [] -> true | _ -> false)
  in
  let* () =
    if constant || List.for_all roles ~f:(function Value_index -> false | _ -> true)
    then Ok ()
    else unsupported declaration.typ_loc
  in
  let* labels =
    Result.all
      (List.map results ~f:(fun (constructor, arguments) ->
           let* labels =
             Result.all
               (List.filter_mapi roles ~f:(fun position role ->
                    match role with
                    | Parameter | Value_index -> None
                    | Constructor_index ->
                        Some
                          (match
                             row_tags ~required:true (List.nth_exn arguments position)
                           with
                          | Ok (_, [ label ]) -> Ok (position, label)
                          | Ok _ | Error () -> unsupported constructor.cd_loc)))
           in
           Ok (String.uncapitalize constructor.cd_name.txt, labels)))
  in
  let* () =
    List.fold_result results ~init:() ~f:(fun () (constructor, arguments) ->
        let ordinary =
          List.filter_map (List.zip_exn roles arguments) ~f:(fun (role, argument) ->
              match role with
              | Parameter -> Some argument
              | Value_index | Constructor_index -> None)
        in
        let rec payload seen environment typ =
          let id = Types.get_id typ in
          if Set.mem seen id then true
          else
            let seen = Set.add seen id in
            match Types.get_desc typ with
            | Tvar _ | Tunivar _ -> List.exists ordinary ~f:(Types.eq_type typ)
            | Tconstr (path, arguments, _) ->
                let roles =
                  try Some (compiler_roles (Env.find_type path environment))
                  with Stdlib.Not_found -> None
                in
                let arguments =
                  match roles with
                  | Some roles when List.length roles = List.length arguments ->
                      List.filter_map (List.zip_exn roles arguments)
                        ~f:(fun (role, argument) ->
                          match role with
                          | Parameter -> Some argument
                          | Value_index | Constructor_index -> None)
                  | Some _ | None -> arguments
                in
                List.for_all arguments ~f:(fun argument ->
                    Result.is_ok (row_tags ~required:false argument)
                    || payload seen environment argument)
            | Tvariant _ -> false
            | _ ->
                Btype.fold_type_expr
                  (fun valid child -> valid && payload seen environment child)
                  true typ
        in
        let check (typ : Typedtree.core_type) =
          payload (Set.empty (module Int)) typ.ctyp_env typ.ctyp_type
        in
        let supported =
          match constructor.cd_args with
          | Cstr_tuple arguments -> List.for_all arguments ~f:check
          | Cstr_record fields ->
              List.for_all fields ~f:(fun field -> check field.Typedtree.ld_type)
        in
        if supported then Ok () else unsupported constructor.cd_loc)
  in
  Ok
    {
      roles;
      indices = List.map roles ~f:(function Parameter -> false | _ -> true);
      results =
        List.map results ~f:(fun (constructor, arguments) ->
            (String.uncapitalize constructor.cd_name.txt, arguments));
      labels;
      constant;
    }

let allowed ~result metadata arguments =
  let* bounds =
    Result.all
      (List.filter_mapi metadata.roles ~f:(fun position role ->
           match role with
           | Parameter | Value_index -> None
           | Constructor_index ->
               Some
                 (match row_tags ~required:result (List.nth_exn arguments position) with
                 | Ok (closed, labels) -> Ok (position, closed, labels)
                 | Error () -> Error ())))
  in
  Ok
    (List.filter_map metadata.labels ~f:(fun (constructor, labels) ->
         Option.some_if
           (List.for_all labels ~f:(fun (position, label) ->
                match
                  List.find bounds ~f:(fun (index, _, _) -> Int.equal index position)
                with
                | Some (_, closed, allowed) ->
                    ((not result) && not closed)
                    || List.mem allowed label ~equal:String.equal
                | None -> true))
           constructor))
