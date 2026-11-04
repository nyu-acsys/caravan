(** Imported signature namespaces, with their compiler paths and source scopes. *)

open Base

let ( let* ) = Result.( >>= )

type t = {
  library_name : string;
  library_id : Ident.t;
  library_path : Path.t;
  source_name : string;
  library : Source.interface;
}

type named_signature = {
  declaration : Typedtree.module_type_declaration;
  interface : Source.interface;
}

let environment (source : Source.t) library =
  match Env.open_signature Asttypes.Override library.library_path source.env with
  | Ok environment -> Ok environment
  | Error (`Not_found | `Functor) ->
      Error
        (Report.error Type library.library.scope.location
           ("Cannot resolve imported module " ^ library.source_name))

(** Source declarations retain the compiler variables of parameterized abstract types. *)
let abstract_types library =
  match library.library.typed_signature with
  | None ->
      Report.unsupported library.library.scope.location
        "An imported interface without a typed signature"
  | Some signature ->
      List.fold_result signature.sig_items ~init:[] ~f:(fun declarations item ->
          match item.Typedtree.sig_desc with
          | Tsig_type (_, types) ->
              let* types =
                List.map types ~f:(fun declaration ->
                    match (declaration.Typedtree.typ_kind, declaration.typ_manifest) with
                    | Ttype_abstract, None -> Ok declaration
                    | _ ->
                        Report.unsupported declaration.typ_loc
                          "A library type other than an abstract type")
                |> Result.all
              in
              Ok (declarations @ types)
          | _ -> Ok declarations)

let contains (outer : Location.t) (inner : Location.t) =
  outer.loc_start.pos_cnum <= inner.loc_start.pos_cnum
  && inner.loc_end.pos_cnum <= outer.loc_end.pos_cnum

let direct_comments (interface : Source.interface) (signature : Typedtree.signature) scope
    =
  let nested =
    List.filter_map signature.sig_items ~f:(fun item ->
        match item.sig_desc with
        | Tsig_module _ | Tsig_modtype _ -> Some item.sig_loc
        | _ -> None)
  in
  let items = signature.sig_items in
  let nexts =
    List.map (List.drop items 1) ~f:(fun item -> Some item.Typedtree.sig_loc) @ [ None ]
  in
  let comments =
    List.filter interface.interface_comments ~f:(fun (_, location) ->
        contains scope.Declaration_scope.location location
        && not (List.exists nested ~f:(fun nested -> contains nested location)))
  in
  let* () =
    List.fold_result (Annotation.of_comments comments) ~init:() ~f:(fun () annotation ->
        match Annotation.kind annotation with
        | Contract ->
            if
              List.exists (List.zip_exn items nexts) ~f:(fun (item, next) ->
                  match item.sig_desc with
                  | Tsig_value _ ->
                      Declaration_scope.following ~scope ~item_loc:item.sig_loc ~next
                        annotation.loc
                  | _ -> false)
            then Ok ()
            else
              Error
                (Report.error Type annotation.loc
                   "This contract is outside an imported value declaration")
        | Ghost_module -> Ok ()
        | Loop | Predicate | Ghost | Scope | Returns | Proof | Manual | Linearization
        | Initially | Initializes | Trusted ->
            Ok ())
  in
  Ok comments

let flatten libraries =
  let rec collect_signature interface signature =
    List.fold_result signature.Typedtree.sig_items ~init:[] ~f:(fun names item ->
        let* added =
          match item.sig_desc with
          | Tsig_value _ | Tsig_type _ | Tsig_attribute _ | Tsig_exception _ -> Ok []
          | Tsig_module declaration -> collect_type interface declaration.md_type
          | Tsig_modtype declaration ->
              begin match declaration.mtd_type with
              | None ->
                  Report.unsupported declaration.mtd_loc "Abstract imported module types"
              | Some module_type ->
                  let* nested = collect_type interface module_type in
                  Ok ({ declaration; interface } :: nested)
              end
          | Tsig_typesubst _ | Tsig_modsubst _ | Tsig_modtypesubst _ ->
              Report.unsupported item.sig_loc "Imported signature substitutions"
          | Tsig_recmodule _ ->
              Report.unsupported item.sig_loc "Recursive imported modules"
          | Tsig_open _ -> Report.unsupported item.sig_loc "Explicit signature opens"
          | Tsig_include _ -> Report.unsupported item.sig_loc "Signature includes"
          | Tsig_typext _ | Tsig_class _ | Tsig_class_type _ ->
              Report.unsupported item.sig_loc "This item of a library's interface"
        in
        Ok (List.rev_append added names))
  and collect_type interface (module_type : Typedtree.module_type) =
    match module_type.mty_desc with
    | Tmty_signature signature -> collect_signature interface signature
    | Tmty_ident _ | Tmty_alias _ -> Ok []
    | Tmty_functor _ -> Report.unsupported module_type.mty_loc "Imported functors"
    | Tmty_with _ -> Report.unsupported module_type.mty_loc "Imported with constraints"
    | Tmty_typeof _ ->
        Report.unsupported module_type.mty_loc "Imported module type of expressions"
  in
  let* names =
    List.fold_result libraries ~init:[] ~f:(fun names (library : Source.library) ->
        match library.library.typed_signature with
        | None ->
            Report.unsupported library.library.scope.location
              "An imported interface without a typed signature"
        | Some signature ->
            let* added = collect_signature library.library signature in
            Ok (List.rev_append added names))
  in
  let named_type (module_type : Typedtree.module_type) path =
    let direct =
      List.find names ~f:(fun named -> Path.same path (Pident named.declaration.mtd_id))
    in
    match direct with
    | Some _ -> Ok direct
    | None ->
        begin try
          let declaration = Env.find_modtype path module_type.mty_env in
          Ok
            (List.find names ~f:(fun named ->
                 Shape.Uid.equal named.declaration.mtd_uid declaration.mtd_uid))
        with exn ->
          Error
            (Option.value (Report.of_exn exn)
               ~default:
                 (Report.error Type module_type.mty_loc (Stdlib.Printexc.to_string exn)))
        end
  in
  let rec resolve seen interface (module_type : Typedtree.module_type) =
    match module_type.mty_desc with
    | Tmty_signature signature ->
        Ok
          (Some
             (interface, signature, Declaration_scope.{ location = module_type.mty_loc }))
    | Tmty_alias _ -> Ok None
    | Tmty_ident (path, _) ->
        if List.mem seen path ~equal:Path.same then
          Report.unsupported module_type.mty_loc "Cyclic imported module types"
        else
          let* named = named_type module_type path in
          begin match named with
          | Some { declaration = { mtd_type = Some definition; _ }; interface } ->
              resolve (path :: seen) interface definition
          | Some { declaration = { mtd_type = None; _ }; _ } | None ->
              Report.unsupported module_type.mty_loc
                "An imported module type without a supported source signature"
          end
    | Tmty_functor _ -> Report.unsupported module_type.mty_loc "Imported functors"
    | Tmty_with _ -> Report.unsupported module_type.mty_loc "Imported with constraints"
    | Tmty_typeof _ ->
        Report.unsupported module_type.mty_loc "Imported module type of expressions"
  in
  let* () =
    List.fold_result names ~init:() ~f:(fun () named ->
        match named.declaration.mtd_type with
        | None -> Ok ()
        | Some definition ->
            let* resolved = resolve [] named.interface definition in
            begin match resolved with
            | None -> Ok ()
            | Some (interface, signature, scope) ->
                Result.map (direct_comments interface signature scope) ~f:(fun _ -> ())
            end)
  in
  let rec namespace ~library_name ~library_id ~library_path ~source_name interface
      (signature : Typedtree.signature) scope =
    let* interface_comments = direct_comments interface signature scope in
    let own_items =
      List.filter signature.sig_items ~f:(fun item ->
          match item.sig_desc with
          | Tsig_value _ | Tsig_type _ | Tsig_attribute _ -> true
          | _ -> false)
    in
    let own_types =
      List.filter signature.sig_type ~f:(function
        | Types.Sig_value _ | Sig_type _ -> true
        | Sig_typext _ | Sig_module _ | Sig_modtype _ | Sig_class _ | Sig_class_type _ ->
            false)
    in
    let typed_signature =
      { signature with sig_items = own_items; sig_type = own_types }
    in
    let library =
      {
        Source.signature = Untypeast.untype_signature typed_signature;
        typed_signature = Some typed_signature;
        interface_comments;
        scope;
      }
    in
    let current = { library_name; library_id; library_path; source_name; library } in
    let* children =
      List.fold_result signature.sig_items ~init:[] ~f:(fun children item ->
          match item.sig_desc with
          | Tsig_module { md_name = { txt = Some name; _ }; md_type; _ } ->
              let* resolved = resolve [] interface md_type in
              begin match resolved with
              | None -> Ok children
              | Some (interface, signature, scope) ->
                  let source_name = source_name ^ "." ^ name in
                  let library_name =
                    Fresh_names.fresh (String.tr source_name ~target:'.' ~replacement:'_')
                  in
                  let library_id = Ident.create_local library_name in
                  let library_path = Path.Pdot (library_path, name) in
                  let* nested =
                    namespace ~library_name ~library_id ~library_path ~source_name
                      interface signature scope
                  in
                  Ok (List.rev_append nested children)
              end
          | Tsig_module _ -> Report.unsupported item.sig_loc "Anonymous imported modules"
          | _ -> Ok children)
    in
    Ok (current :: List.rev children)
  in
  let* flattened =
    List.fold_result libraries ~init:[] ~f:(fun flattened (library : Source.library) ->
        match library.library.typed_signature with
        | None ->
            Report.unsupported library.library.scope.location
              "An imported interface without a typed signature"
        | Some signature ->
            let* namespaces =
              namespace ~library_name:library.library_name ~library_id:library.library_id
                ~library_path:(Pident library.library_id)
                ~source_name:library.library_name library.library signature
                library.library.scope
            in
            Ok (List.rev_append namespaces flattened))
  in
  Ok (List.rev flattened)
