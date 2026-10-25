(** Checks public contracts before implementation representations are substituted. *)

open Base
module S = Caravan_spec.Spec_ast

let ( let* ) = Result.( >>= )

let compiler ~at f =
  try Ok (f ())
  with exn ->
    Error
      (Option.value (Report.of_exn exn)
         ~default:(Report.error Type at (Stdlib.Printexc.to_string exn)))

let rec monotype typ =
  match Types.get_desc typ with Tpoly (typ, []) -> monotype typ | _ -> typ

let rec arguments typ =
  match Types.get_desc typ with
  | Tpoly (typ, []) -> arguments typ
  | Tarrow (_, argument, result, _) ->
      let rest, result = arguments result in
      (monotype argument :: rest, result)
  | _ -> ([], monotype typ)

let rec determined typ =
  match Types.get_desc typ with
  | Tvar _ | Tunivar _ -> false
  | Tpoly (typ, []) -> determined typ
  | _ -> true

let terms ?expected ?(logical_types = []) ?(restricted = false) ?(proof_ids = [])
    ?(predicates = fun _ -> None) ~environment ~variables terms =
  let at =
    Option.value_map (List.hd terms) ~default:Location.none ~f:(fun term ->
        term.S.term_loc)
  in
  let synthetic name = S.mk_id ~loc:at ("caravan$public$" ^ name) in
  let variable id = S.mk_term (S.Tvar (Qid id)) id.S.pid_loc in
  let logical_substitution =
    List.fold logical_types ~init:Subst.identity ~f:(fun substitution descriptor ->
        match (descriptor.Datatypes.mathematical_integer, descriptor.id) with
        | true, Some id -> Subst.add_type id Predef.path_int substitution
        | _ -> substitution)
  in
  let normalize typ = Subst.type_expr logical_substitution (monotype typ) in
  let infer ?(functions = []) variables term =
    Source.infer_logical_expression environment ~functions
      ~variables:
        (List.filter_map variables ~f:(fun (name, typ) ->
             Option.map typ ~f:(fun typ -> (name, normalize typ))))
      term
  in
  let compatible ~at expected actual =
    let expected = normalize expected in
    let actual = normalize actual in
    if not (determined expected && determined actual) then Ok ()
    else
      let* equal =
        compiler ~at (fun () -> Ctype.is_equal environment false [ expected ] [ actual ])
      in
      if equal then Ok ()
      else
        let* contextual =
          compiler ~at (fun () ->
              Ctype.does_match environment actual expected
              || Ctype.does_match environment expected actual)
        in
        if contextual then Ok ()
        else
          Error
            (Report.error Type at
               (Printtyp.wrap_printing_env ~error:true environment (fun () ->
                    Stdlib.Format.asprintf
                      "This specification has type %a, but %a is required"
                      Printtyp.type_expr actual Printtyp.type_expr expected)))
  in
  let require ~at expected = function
    | None -> Ok ()
    | Some actual -> compatible ~at expected actual
  in
  let opaque_location location typ =
    match location.S.term_desc with
    | Tfield _ -> Ok ()
    | _ ->
        compiler ~at:location.term_loc (fun () ->
            match Types.get_desc (monotype typ) with
            | Tconstr ((Pident _ as path), _, _) ->
                let declaration = Env.find_type path environment in
                let logical =
                  List.exists logical_types ~f:(fun descriptor ->
                      (descriptor.Datatypes.mathematical_integer
                      || Option.is_some descriptor.collection)
                      && Option.exists descriptor.id ~f:(fun id ->
                          Path.same path (Pident id)))
                in
                (not logical)
                && ((match declaration.type_kind with
                      | Type_abstract _ -> Option.is_none declaration.type_manifest
                      | _ -> false)
                   || Poly.equal declaration.type_private Asttypes.Private)
            | _ -> false)
        |> Result.bind ~f:(function
          | false -> Ok ()
          | true ->
              Error
                (Report.error Type location.term_loc
                   "Ownership of an abstract module type must be exposed through a \
                    predicate"))
  in
  let rec list_literal (term : S.term) =
    match term.term_desc with
    | Tvar (Qid { pid_str = "[]"; _ }) -> true
    | Tapply
        ( {
            term_desc = Tapply ({ term_desc = Tvar (Qid { pid_str = "::"; _ }); _ }, _);
            _;
          },
          tail ) ->
        list_literal tail
    | _ -> false
  in
  let sequence_list typ =
    compiler ~at (fun () ->
        match Types.get_desc (Ctype.expand_head environment (monotype typ)) with
        | Tconstr (path, [ element ], _)
          when List.exists logical_types ~f:(fun descriptor ->
                   Datatypes.is_sequence descriptor
                   && Option.exists descriptor.id ~f:(fun id ->
                       Path.same path (Pident id))) ->
            Some (Ctype.newconstr Predef.path_list [ element ])
        | _ -> None)
  in
  let equality left left_type right right_type =
    let* left_context = if list_literal right then sequence_list left_type else Ok None in
    match left_context with
    | Some expected -> compatible ~at:right.S.term_loc expected right_type
    | None ->
        let* right_context =
          if list_literal left then sequence_list right_type else Ok None
        in
        begin match right_context with
        | Some expected -> compatible ~at:left.S.term_loc expected left_type
        | None -> compatible ~at:right.S.term_loc left_type right_type
        end
  in
  let collection ?(map = false) ~at = function
    | None -> Ok None
    | Some typ when not (determined typ) -> Ok None
    | Some typ ->
        let* shape =
          compiler ~at (fun () ->
              let private_head =
                match Types.get_desc (monotype typ) with
                | Tconstr (path, _, _) ->
                    Poly.equal (Env.find_type path environment).type_private
                      Asttypes.Private
                | _ -> false
              in
              if private_head then None
              else
                match Types.get_desc (Ctype.expand_head environment (monotype typ)) with
                | Tconstr (path, [ element ], _) when Path.same path Predef.path_list ->
                    Some (Predef.type_int, element)
                | Tconstr (path, arguments, _) ->
                    List.find_map logical_types ~f:(fun descriptor ->
                        if
                          Option.exists descriptor.Datatypes.id ~f:(fun id ->
                              Path.same path (Pident id))
                        then
                          match (descriptor.collection, arguments) with
                          | Some Sequence, [ element ] -> Some (Predef.type_int, element)
                          | Some Map, [ key; value ] when map -> Some (key, value)
                          | _ -> None
                        else None)
                | _ -> None)
        in
        begin match shape with
        | Some _ -> Ok shape
        | None ->
            Error
              (Report.error Type at
                 "This collection operation requires a visible collection type")
        end
  in
  let restricted_argument ~at typ =
    compiler ~at (fun () ->
        let rec contains seen typ =
          match Types.get_desc (monotype typ) with
          | Tconstr (path, arguments, _) -> (
              List.exists arguments ~f:(contains seen)
              ||
              match path with
              | Pident id
                when (not (Ident.is_predef id || Ident.persistent id))
                     && (not (List.mem proof_ids id ~equal:Ident.same))
                     && (not
                           (List.exists logical_types ~f:(fun descriptor ->
                                Option.exists descriptor.Datatypes.id ~f:(Ident.same id))))
                     && not (List.mem seen path ~equal:Path.same) ->
                  let declaration = Env.find_type path environment in
                  let seen = path :: seen in
                  if Poly.equal declaration.type_private Asttypes.Private then true
                  else
                    begin match (declaration.type_kind, declaration.type_manifest) with
                    | Type_abstract _, None -> true
                    | _, Some manifest -> contains seen manifest
                    | Type_record (fields, _), None ->
                        List.exists fields ~f:(fun field ->
                            contains seen field.Types.ld_type)
                    | Type_variant (constructors, _), None ->
                        List.exists constructors ~f:(fun constructor ->
                            match constructor.Types.cd_args with
                            | Cstr_tuple arguments ->
                                List.exists arguments ~f:(contains seen)
                            | Cstr_record fields ->
                                List.exists fields ~f:(fun field ->
                                    contains seen field.Types.ld_type))
                    | (Type_open | Type_external _), None -> false
                    end
              | Pident _ | Pdot _ | Papply _ | Pextra_ty _ -> false)
          | Ttuple components ->
              List.exists components ~f:(fun (_, typ) -> contains seen typ)
          | Tarrow (_, argument, result, _) ->
              contains seen argument || contains seen result
          | _ -> false
        in
        contains [] typ)
  in
  let constructor q =
    match Source.constructor environment q with
    | Some description -> Ok description
    | None ->
        Error
          (Report.error Type (S.qualid_loc q)
             "This constructor is not visible in the signature")
  in
  let rec pattern (p : S.pat) =
    match p.pat_desc with
    | Pwild | Pid _ | Pconst _ -> Ok ()
    | Ptuple patterns ->
        Result.map (Result.all (List.map patterns ~f:pattern)) ~f:(fun _ -> ())
    | Pcast (p, typ) ->
        let* _ = Source.ocaml_type environment ~at:p.pat_loc typ in
        pattern p
    | Pconstr (q, argument) ->
        let* _ = constructor q in
        Option.value_map argument ~default:(Ok ()) ~f:pattern
  in
  let bind_pattern variables (p : S.pat) typ =
    let names = Source.logical_pattern_names p in
    let typ = Option.value typ ~default:(Ctype.newvar ()) in
    let rhs = synthetic "pattern" in
    let terms = List.map names ~f:(fun name -> variable (S.mk_id ~loc:p.pat_loc name)) in
    let body =
      match terms with [ term ] -> term | _ -> S.mk_term (Ttuple terms) p.pat_loc
    in
    let fallback = synthetic "pattern_fallback" in
    let wildcard = S.{ pat_desc = Pwild; pat_loc = p.pat_loc } in
    let term =
      S.mk_term
        (Tmatch (variable rhs, [ (p, body); (wildcard, variable fallback) ]))
        p.pat_loc
    in
    let* bound =
      infer [ (rhs.pid_str, Some typ); (fallback.pid_str, Some (Ctype.newvar ())) ] term
    in
    let types =
      match (names, Types.get_desc bound) with
      | [ _ ], _ -> [ bound ]
      | _, Ttuple types -> List.map types ~f:snd
      | _ -> []
    in
    if List.length names = List.length types then
      Ok
        (List.map2_exn names types ~f:(fun name typ ->
             (name, Option.some_if (determined typ) typ))
        @ variables)
    else
      Error
        (Report.error Type p.pat_loc
           "The signature pattern's variable types could not be determined")
  in
  let lookup variables q =
    match q with
    | S.Qid id ->
        begin match List.Assoc.find variables id.pid_str ~equal:String.equal with
        | Some typ -> Ok typ
        | None ->
            begin match Source.value_path environment q with
            | None when Option.is_some (Source.logical_builtin_path ~functions:[] q) ->
                Result.map
                  (infer variables (S.mk_term (Tvar q) (S.qualid_loc q)))
                  ~f:Option.some
            | None -> Ok None
            | Some path ->
                compiler ~at:id.pid_loc (fun () ->
                    Some (Env.find_value path environment).val_type)
            end
        end
    | Qdot _ ->
        begin match Source.value_path environment q with
        | None when Option.is_some (Source.logical_builtin_path ~functions:[] q) ->
            Result.map
              (infer variables (S.mk_term (Tvar q) (S.qualid_loc q)))
              ~f:Option.some
        | None -> Ok None
        | Some path ->
            compiler ~at:(S.qualid_loc q) (fun () ->
                Some (Env.find_value path environment).val_type)
        end
  in
  let rec apply variables (term : S.term) callee arguments =
    let* types = Result.all (List.map arguments ~f:(walk variables)) in
    let primitive =
      match callee.S.term_desc with
      | Tvar (Qid ({ pid_str = "length" | "last" | "drop" | "take"; _ } as id))
        when Option.is_some (Source.value_path environment (Qid id)) ->
          None
      | Tvar (Qid id) -> Some id.pid_str
      | _ -> None
    in
    let all expected =
      Result.map
        (Result.all
           (List.map2_exn arguments types ~f:(fun argument typ ->
                require ~at:argument.S.term_loc expected typ)))
        ~f:(fun _ -> ())
    in
    let predicate = match callee.S.term_desc with Tvar q -> predicates q | _ -> None in
    match predicate with
    | Some expected ->
        let rec consume expected arguments types =
          match (expected, arguments, types) with
          | _, [], [] -> Ok ()
          | expected :: rest, argument :: arguments, actual :: types ->
              let* contextual =
                if list_literal argument then sequence_list expected else Ok None
              in
              let* () =
                require ~at:argument.S.term_loc
                  (Option.value contextual ~default:expected)
                  actual
              in
              consume rest arguments types
          | [], _ :: _, _ :: _ ->
              Error
                (Report.error Type term.term_loc
                   "This predicate call supplies too many arguments")
          | _ ->
              Error
                (Report.error Type term.term_loc
                   "The predicate argument types could not be determined")
        in
        let* () = consume expected arguments types in
        Ok (Some Predef.type_bool)
    | None -> (
        match (primitive, arguments, types) with
        | Some ("length" | "last"), [ argument ], [ typ ] ->
            let* shape = collection ~at:argument.term_loc typ in
            if Poly.equal primitive (Some "length") then Ok (Some Predef.type_int)
            else Ok (Option.map shape ~f:snd)
        | Some ("drop" | "take"), [ count; argument ], [ count_type; typ ] ->
            let* () = require ~at:count.term_loc Predef.type_int count_type in
            let* _ = collection ~at:argument.term_loc typ in
            Ok typ
        | Some "([])", [ argument; index ], [ typ; index_type ] ->
            let* shape = collection ~map:true ~at:argument.term_loc typ in
            let* () =
              Option.value_map shape ~default:(Ok ()) ~f:(fun (key, _) ->
                  require ~at:index.term_loc key index_type)
            in
            Ok (Option.map shape ~f:snd)
        | Some ("++" | "@"), [ left; right ], [ left_type; right_type ] ->
            let* left_shape = collection ~at:left.term_loc left_type in
            let* right_shape = collection ~at:right.term_loc right_type in
            let* () =
              match (left_shape, right_shape) with
              | Some (_, left), Some (_, right) -> compatible ~at:term.term_loc left right
              | _ -> Ok ()
            in
            Ok (Option.first_some left_type right_type)
        | Some "own", location :: _, Some typ :: _ ->
            let* () = opaque_location location typ in
            Ok None
        | Some ("+" | "-" | "*" | "/" | "mod" | "~-"), _, _ ->
            let* () = all Predef.type_int in
            Ok (Some Predef.type_int)
        | Some ("<" | "<=" | ">" | ">="), _, _ ->
            let* () = all Predef.type_int in
            Ok (Some Predef.type_bool)
        | Some ("&&" | "||" | "/\\" | "\\/" | "->" | "<->" | "not"), _, _ ->
            let* () = all Predef.type_bool in
            Ok (Some Predef.type_bool)
        | ( Some ("=" | "<>" | "==" | "!=" | "===" | "=/="),
            [ left_term; right_term ],
            [ Some left; Some right ] ) ->
            let* () = equality left_term left right_term right in
            Ok (Some Predef.type_bool)
        | Some ("=" | "<>" | "==" | "!=" | "===" | "=/="), _, _ ->
            Ok (Some Predef.type_bool)
        | _ ->
            let* callee_type = walk variables callee in
            let* () =
              if restricted && Option.is_none callee_type then
                let* restricted_arguments =
                  Result.all
                    (List.map2_exn arguments types ~f:(fun argument typ ->
                         Option.value_map typ ~default:(Ok false)
                           ~f:(restricted_argument ~at:argument.S.term_loc)))
                in
                if List.exists restricted_arguments ~f:Fn.id then
                  Report.unsupported term.term_loc
                    "A predicate call involving an abstract signature type"
                else Ok ()
              else Ok ()
            in
            let rec consume typ arguments types =
              match (typ, arguments, types) with
              | _, [], [] -> Ok typ
              | Some typ, argument :: arguments, actual :: types ->
                  begin match Types.get_desc typ with
                  | Tpoly (typ, []) ->
                      consume (Some typ) (argument :: arguments) (actual :: types)
                  | Tarrow (_, expected, result, _) ->
                      let* () = require ~at:argument.S.term_loc expected actual in
                      consume (Some result) arguments types
                  | _ -> Ok None
                  end
              | None, _ :: arguments, _ :: types -> consume None arguments types
              | _ -> Ok None
            in
            let* result = consume callee_type arguments types in
            if Option.is_some callee_type then
              let rec placeholder name (argument : S.term) typ =
                match (argument.term_desc, Types.get_desc (monotype typ)) with
                | Ttuple arguments, Ttuple types
                  when List.length arguments = List.length types ->
                    let components =
                      List.mapi (List.zip_exn arguments types)
                        ~f:(fun index (argument, (_, typ)) ->
                          placeholder (name ^ "$" ^ Int.to_string index) argument typ)
                    in
                    ( S.mk_term (Ttuple (List.map components ~f:fst)) argument.term_loc,
                      List.concat_map components ~f:snd )
                | _ ->
                    let name =
                      match argument.term_desc with
                      | Tvar (Qid original) -> original
                      | _ -> S.mk_id ~loc:argument.term_loc ("caravan$public$" ^ name)
                    in
                    (variable name, [ (name.pid_str, Some typ) ])
              in
              let placeholders =
                List.mapi (List.zip_exn arguments types) ~f:(fun index (argument, typ) ->
                    placeholder
                      ("argument" ^ Int.to_string index)
                      argument
                      (Option.value typ ~default:(Ctype.newvar ())))
              in
              let expression =
                List.fold placeholders ~init:callee ~f:(fun callee (argument, _) ->
                    S.mk_term (Tapply (callee, argument)) term.term_loc)
              in
              let functions =
                match callee.term_desc with
                | Tvar q when Option.is_some (Source.value_path environment q) ->
                    [ Qualified_name.to_string (Qualified_name.of_spec q) ]
                | _ -> []
              in
              let* typ =
                Result.map_error
                  (infer ~functions
                     (List.concat_map placeholders ~f:snd @ variables)
                     expression)
                  ~f:(fun error ->
                    let message =
                      List.fold (List.concat_map placeholders ~f:snd)
                        ~init:error.Report.message ~f:(fun message (name, _) ->
                          if String.is_prefix name ~prefix:"caravan$public$argument" then
                            String.substr_replace_all message
                              ~pattern:("The value " ^ name) ~with_:"This argument"
                          else message)
                    in
                    { error with message })
              in
              Ok (Some typ)
            else Ok result)
  and walk variables (term : S.term) =
    match term.term_desc with
    | Ttrue | Tfalse -> Ok (Some Predef.type_bool)
    | Tconst _ | Ttuple [] -> Result.map (infer variables term) ~f:Option.some
    | Tvar q when Source.logical_constructor q ->
        let* description = constructor q in
        let* () =
          if Poly.equal description.cstr_private Asttypes.Private then
            Error
              (Report.error Type term.term_loc
                 "A specification cannot construct a value of a private type")
          else Ok ()
        in
        let arguments =
          match (q, description.cstr_args) with
          | Qid { pid_str = "::"; _ }, arguments -> arguments
          | _, ([] | [ _ ]) -> description.cstr_args
          | _, arguments ->
              [ Ctype.newty (Ttuple (List.map arguments ~f:(fun typ -> (None, typ)))) ]
        in
        let typ =
          List.fold_right arguments ~init:description.cstr_res ~f:(fun argument result ->
              Ctype.newty (Tarrow (Nolabel, argument, result, Types.commu_ok)))
        in
        Ok (Some typ)
    | Tvar q -> lookup variables q
    | Tapply _ ->
        let rec split arguments (term : S.term) =
          match term.term_desc with
          | Tapply (callee, argument) -> split (argument :: arguments) callee
          | _ -> (term, arguments)
        in
        let callee, arguments = split [] term in
        apply variables term callee arguments
    | Tinfix _ -> walk variables (S.chain term)
    | Tfield (base, field) ->
        let* typ = walk variables base in
        begin match typ with
        | None -> Ok None
        | Some typ ->
            let name = synthetic "field" in
            let expression = S.mk_term (Tfield (variable name, field)) term.term_loc in
            let* is_list =
              compiler ~at:base.term_loc (fun () ->
                  match Types.get_desc (Ctype.expand_head environment typ) with
                  | Tconstr (path, _, _) -> Path.same path Predef.path_list
                  | _ -> false)
            in
            let* typ =
              Source.infer_logical_expression
                ~is_list:(fun _ -> is_list)
                environment ~functions:[]
                ~variables:[ (name.pid_str, typ) ]
                expression
            in
            Ok (Some typ)
        end
    | Tif (condition, yes, no) ->
        let* condition_type = walk variables condition in
        let* () = require ~at:condition.term_loc Predef.type_bool condition_type in
        let* yes_type = walk variables yes in
        let* no_type = walk variables no in
        let* () =
          match (yes_type, no_type) with
          | Some yes, Some no -> compatible ~at:term.term_loc yes no
          | _ -> Ok ()
        in
        Ok (Option.first_some yes_type no_type)
    | Tquant (_, binders, body) ->
        let* added =
          Result.all
            (List.map binders ~f:(fun (id, typ) ->
                 let* typ =
                   Option.value_map typ ~default:(Ok None) ~f:(fun typ ->
                       Result.map
                         (Source.ocaml_type environment ~at:id.S.pid_loc typ)
                         ~f:Option.some)
                 in
                 Ok (id.S.pid_str, typ)))
        in
        let* typ = walk (added @ variables) body in
        let* () = require ~at:body.term_loc Predef.type_bool typ in
        Ok (Some Predef.type_bool)
    | Tcomprehension ((id, typ), body) ->
        let* typ = Source.ocaml_type environment ~at:id.pid_loc typ in
        let* body_type = walk ((id.pid_str, Some typ) :: variables) body in
        let* () = require ~at:body.term_loc Predef.type_bool body_type in
        Ok None
    | Tlet (p, rhs, body) ->
        let* () = pattern p in
        let* typ = walk variables rhs in
        let* variables = bind_pattern variables p typ in
        walk variables body
    | Tmatch (value, cases) ->
        let* typ = walk variables value in
        let* results =
          Result.all
            (List.map cases ~f:(fun (p, body) ->
                 let* () = pattern p in
                 let* variables = bind_pattern variables p typ in
                 walk variables body))
        in
        let known = List.filter_opt results in
        begin match known with
        | [] -> Ok None
        | first :: rest ->
            let* _ = Result.all (List.map rest ~f:(compatible ~at:term.term_loc first)) in
            Ok (Some first)
        end
    | Tcast (value, typ) ->
        let* expected = Source.ocaml_type environment ~at:term.term_loc typ in
        let* actual = walk variables value in
        let* () = require ~at:term.term_loc expected actual in
        Ok (Some expected)
    | Ttuple values ->
        let* types = Result.all (List.map values ~f:(walk variables)) in
        Ok
          (Some
             (Ctype.newty
                (Ttuple
                   (List.map types ~f:(fun typ ->
                        (None, Option.value typ ~default:(Ctype.newvar ())))))))
    | Tattr (_, value) | Told value -> walk variables value
  in
  let variables = List.map variables ~f:(fun (name, typ) -> (name, Some typ)) in
  Result.map
    (Result.all
       (List.map terms ~f:(fun term ->
            let* typ = walk variables term in
            Option.value_map expected ~default:(Ok ()) ~f:(fun expected ->
                let* contextual =
                  if list_literal term then sequence_list expected else Ok None
                in
                require ~at:term.S.term_loc
                  (Option.value contextual ~default:expected)
                  typ))))
    ~f:(fun _ -> ())

let expression ?(logical_types = []) ?predicates ~environment ~variables term =
  terms ~logical_types ?predicates ~environment ~variables [ term ]

let check ?(logical_types = []) ?(restricted = false) ?predicates ?environment source
    (signature : Module_inventory.signature_value) (contract : S.contract) =
  let logical_types =
    match source.Source.sequence with
    | Pident id -> Datatypes.sequence id :: logical_types
    | Pdot _ | Papply _ | Pextra_ty _ -> logical_types
  in
  let environment =
    Option.value environment
      ~default:(Source.annotation_env source signature.site.environment)
  in
  let proof_ids =
    List.map source.spec_bindings ~f:(function
        | Types.Sig_value (id, _, _)
        | Sig_type (id, _, _, _)
        | Sig_module (id, _, _, _, _)
        | Sig_modtype (id, _, _)
        | Sig_typext (id, _, _, _)
        | Sig_class (id, _, _, _)
        | Sig_class_type (id, _, _, _)
        -> id)
  in
  let at = signature.declaration.val_loc in
  let argument_types, result_type = arguments signature.declaration.val_val.val_type in
  let* variables =
    match contract.header with
    | None -> Ok [ ("result", result_type) ]
    | Some header ->
        let concrete =
          List.filter header.hd_args ~f:(function S.Lghost _ -> false | _ -> true)
        in
        let* inputs =
          if List.length concrete <> List.length argument_types then
            Error
              (Report.error Type at "The contract names the wrong number of arguments")
          else
            Ok
              (List.filter_map (List.zip_exn concrete argument_types) ~f:(function
                | S.Lvar id, typ -> Some (id.pid_str, typ)
                | (Lwild | Lunit _ | Lghost _), _ -> None))
        in
        let* ghosts =
          Result.all
            (List.filter_map (header.hd_args @ header.hd_ret) ~f:(function
              | S.Lghost (id, typ) ->
                  Some
                    (Result.map (Source.ocaml_type environment ~at:id.pid_loc typ)
                       ~f:(fun typ -> (id.pid_str, typ)))
              | Lwild | Lunit _ | Lvar _ -> None))
        in
        let result =
          List.find_map header.hd_ret ~f:(function
            | S.Lvar id -> Some id.pid_str
            | Lwild | Lunit _ | Lghost _ -> None)
        in
        Ok ((Option.value result ~default:"result", result_type) :: (inputs @ ghosts))
  in
  let* () =
    terms ~logical_types ~restricted ~proof_ids ?predicates ~environment ~variables
      ~expected:Predef.type_bool
      (contract.requires @ contract.ensures @ contract.atomic_requires
     @ contract.atomic_ensures)
  in
  terms ~logical_types ~restricted ~proof_ids ?predicates ~environment ~variables
    ~expected:Predef.type_int contract.variant

(** Lowering shares the implementation's lexical names only when their meanings agree. *)
let lowerable source (view : Module_inventory.signature_value) ~environment
    (contract : S.contract) =
  let original = Source.annotation_env source view.site.environment in
  let environment = Source.annotation_env source environment in
  let unavailable at =
    Report.unsupported at
      "A signature contract whose names have a different implementation scope"
  in
  let check_type at typ =
    let* declared = Source.ocaml_type original ~at typ in
    let declared = Subst.type_expr view.substitution declared in
    let* implemented = Source.ocaml_type environment ~at typ in
    let* equal =
      compiler ~at (fun () ->
          Ctype.is_equal environment false [ declared ] [ implemented ])
    in
    if equal then Ok () else unavailable at
  in
  let rec root = function
    | Path.Pident id -> Some id
    | Pdot (path, _) -> root path
    | Papply _ | Pextra_ty _ -> None
  in
  let proof_path path =
    Option.exists (root path) ~f:(fun root ->
        List.exists source.Source.spec_bindings ~f:(function
            | Types.Sig_value (id, _, _)
            | Sig_type (id, _, _, _)
            | Sig_module (id, _, _, _, _)
            | Sig_modtype (id, _, _)
            | Sig_typext (id, _, _, _)
            | Sig_class (id, _, _, _)
            | Sig_class_type (id, _, _, _)
            -> Ident.same root id))
  in
  let standard_library path =
    Option.exists (root path) ~f:(fun id ->
        Ident.persistent id
        && (String.equal (Ident.name id) "Stdlib"
           || String.is_prefix (Ident.name id) ~prefix:"Stdlib__"))
  in
  let value bound q =
    match q with
    | S.Qid id when List.mem bound id.pid_str ~equal:String.equal -> Ok ()
    | _ ->
        begin match Source.value_path original q with
        | None ->
            begin match Source.value_path environment q with
            | None -> Ok ()
            | Some path when proof_path path -> Ok ()
            | Some _ -> unavailable (S.qualid_loc q)
            end
        | Some path when proof_path path || standard_library path ->
            begin match Source.value_path environment q with
            | Some body when Path.same path body -> Ok ()
            | _ -> unavailable (S.qualid_loc q)
            end
        | Some _ ->
            Report.unsupported (S.qualid_loc q)
              "A signature contract referring to another OCaml value"
        end
  in
  let constructor q =
    match Source.constructor original q with
    | None -> Ok ()
    | Some declared ->
        begin match Source.constructor environment q with
        | None -> unavailable (S.qualid_loc q)
        | Some implemented ->
            let* equal =
              compiler ~at:(S.qualid_loc q) (fun () ->
                  Ctype.is_equal environment false
                    [ Subst.type_expr view.substitution declared.cstr_res ]
                    [ implemented.cstr_res ])
            in
            if equal then Ok () else unavailable (S.qualid_loc q)
        end
  in
  let rec pattern (p : S.pat) =
    match p.pat_desc with
    | Pwild | Pid _ | Pconst _ -> Ok ()
    | Ptuple patterns -> all_patterns patterns
    | Pcast (p, typ) ->
        let* () = check_type p.pat_loc typ in
        pattern p
    | Pconstr (q, argument) ->
        let* () = constructor q in
        Option.value_map argument ~default:(Ok ()) ~f:pattern
  and all_patterns patterns =
    Result.map (Result.all (List.map patterns ~f:pattern)) ~f:(fun _ -> ())
  in
  let rec term bound (t : S.term) =
    match t.term_desc with
    | Ttrue | Tfalse | Tconst _ -> Ok ()
    | Tvar q -> if Source.logical_constructor q then constructor q else value bound q
    | Tfield (base, _) | Tattr (_, base) | Told base -> term bound base
    | Tapply (callee, argument) -> terms bound [ callee; argument ]
    | Tinfix (left, operator, right) ->
        let* () = value bound (Qid operator) in
        terms bound [ left; right ]
    | Tif (condition, yes, no) -> terms bound [ condition; yes; no ]
    | Tquant (_, binders, body) ->
        let* _ =
          Result.all
            (List.map binders ~f:(fun (id, typ) ->
                 Option.value_map typ ~default:(Ok ()) ~f:(check_type id.S.pid_loc)))
        in
        term (List.map binders ~f:(fun (id, _) -> id.S.pid_str) @ bound) body
    | Tcomprehension ((id, typ), body) ->
        let* () = check_type id.pid_loc typ in
        term (id.pid_str :: bound) body
    | Tlet (p, rhs, body) ->
        let* () = pattern p in
        let* () = term bound rhs in
        term (Source.logical_pattern_names p @ bound) body
    | Tmatch (subject, cases) ->
        let* () = term bound subject in
        let* _ =
          Result.all
            (List.map cases ~f:(fun (p, body) ->
                 let* () = pattern p in
                 term (Source.logical_pattern_names p @ bound) body))
        in
        Ok ()
    | Tcast (subject, typ) ->
        let* () = check_type t.term_loc typ in
        term bound subject
    | Ttuple values -> terms bound values
  and terms bound values =
    Result.map (Result.all (List.map values ~f:(term bound))) ~f:(fun _ -> ())
  in
  let* names =
    match contract.header with
    | None -> Ok [ "result" ]
    | Some header ->
        let* names =
          Result.all
            (List.map (header.hd_args @ header.hd_ret) ~f:(function
              | S.Lghost (id, typ) ->
                  let* () = check_type id.pid_loc typ in
                  Ok (Some id.pid_str)
              | Lvar id -> Ok (Some id.pid_str)
              | Lwild | Lunit _ -> Ok None))
        in
        Ok ("result" :: List.filter_opt names)
  in
  terms names
    (contract.requires @ contract.ensures @ contract.atomic_requires
   @ contract.atomic_ensures @ contract.variant)
