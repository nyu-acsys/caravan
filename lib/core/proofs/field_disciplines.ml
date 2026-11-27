(** Compiler field identity, mutability and optional shared-access discipline. *)

open Base

let ( let* ) = Result.( >>= )

type kind = Ordinary | Frozen | Relaxed

type t = {
  record_path : Path.t;
  position : int;
  label_id : Ident.t;
  label : string;
  kind : kind;
  immutable : bool;
  raw : bool;
  value_type : Types.type_expr;
  declared_at : Location.t;
  at : Location.t;
}

let error ?related at message = Error (Report.error ?related Type at message)

let attribute_kind (attribute : Parsetree.attribute) =
  match attribute.attr_name.txt with
  | "caravan.frozen" -> Some Frozen
  | "caravan.relaxed" -> Some Relaxed
  | _ -> None

let obsolete_attribute (attribute : Parsetree.attribute) =
  String.equal attribute.attr_name.txt "caravan.history"

let check_spelling attribute =
  if obsolete_attribute attribute then
    error attribute.attr_loc
      "The [@caravan.history] attribute has been renamed to [@caravan.relaxed]"
  else Ok ()

let attribute_name = function
  | Ordinary -> "ordinary"
  | Frozen -> "caravan.frozen"
  | Relaxed -> "caravan.relaxed"

let kind_name = function
  | Ordinary -> "ordinary"
  | Frozen -> "frozen"
  | Relaxed -> "relaxed"

let parse_attributes attributes =
  let add seen (attribute : Parsetree.attribute) =
    let* () = check_spelling attribute in
    match attribute_kind attribute with
    | None -> Ok seen
    | Some kind ->
        begin match attribute.attr_payload with
        | PStr [] ->
            begin match seen with
            | None -> Ok (Some (kind, attribute.attr_loc))
            | Some (first, first_at) ->
                let related = [ (first_at, "The first field discipline attribute") ] in
                let message =
                  if Poly.equal first kind then
                    "Duplicate [@" ^ attribute_name kind ^ "] field discipline attribute"
                  else "A field cannot use both [@caravan.frozen] and [@caravan.relaxed]"
                in
                error ~related attribute.attr_loc message
            end
        | PStr _ | PSig _ | PTyp _ | PPat _ ->
            error attribute.attr_loc
              ("The [@" ^ attribute_name kind ^ "] field attribute takes no payload")
        end
  in
  let* seen = List.fold_result attributes ~init:None ~f:add in
  Ok (Option.map seen ~f:fst)

let parse_raw ~kind attributes =
  let raw =
    List.filter attributes ~f:(fun attribute ->
        String.equal attribute.Parsetree.attr_name.txt "caravan.raw")
  in
  match raw with
  | [] -> Ok false
  | [ attribute ] ->
      if not (Poly.equal kind (Some Relaxed)) then
        error attribute.attr_loc
          "The [@caravan.raw] attribute requires [@caravan.relaxed]"
      else
        begin match attribute.attr_payload with
        | PStr [] -> Ok true
        | PStr _ | PSig _ | PTyp _ | PPat _ ->
            error attribute.attr_loc "The [@caravan.raw] field attribute takes no payload"
        end
  | attribute :: _ -> error attribute.attr_loc "Duplicate [@caravan.raw] field attribute"

let storage_type field =
  if field.raw then Predef.type_option field.value_type else field.value_type

let shared fields =
  List.exists fields ~f:(fun field -> not (Poly.equal field.kind Ordinary))

let same_field left right =
  Path.same left.record_path right.record_path && Int.equal left.position right.position

let same_slot left right =
  Int.equal left.position right.position
  && String.equal left.label right.label
  &&
  match (left.record_path, right.record_path) with
  | Path.Pextra_ty (_, a), Path.Pextra_ty (_, b) -> Poly.equal a b
  | Pextra_ty _, _ | _, Pextra_ty _ -> false
  | _ -> true

let find fields ~record_path ~position =
  List.find fields ~f:(fun field ->
      Path.same field.record_path record_path && Int.equal field.position position)

let qualify owner id =
  match owner with
  | None -> Path.Pident id
  | Some parent -> Path.Pdot (parent, Ident.name id)

type record_fields = {
  path : Path.t;
  boxed : bool;
  labels : Types.label_declaration list;
}

let records path (declaration : Types.type_declaration) =
  match declaration.type_kind with
  | Type_record (labels, representation) ->
      let boxed =
        match representation with
        | Record_regular | Record_inlined _ -> true
        | Record_float | Record_unboxed _ | Record_extension _ -> false
      in
      [ { path; boxed; labels } ]
  | Type_variant (constructors, representation) ->
      let boxed =
        match representation with Variant_regular -> true | Variant_unboxed -> false
      in
      List.filter_map constructors ~f:(fun constructor ->
          match constructor.Types.cd_args with
          | Cstr_tuple _ -> None
          | Cstr_record labels ->
              let path = Path.Pextra_ty (path, Pcstr_ty (Ident.name constructor.cd_id)) in
              Some { path; boxed; labels })
  | Type_abstract _ | Type_open | Type_external _ -> []

let field_metadata ~canonicalize { path; boxed; labels } =
  let heap =
    List.exists labels ~f:(fun label -> Poly.equal label.Types.ld_mutable Mutable)
  in
  let record_path = canonicalize path in
  let field position (label : Types.label_declaration) =
    let* discipline = parse_attributes label.ld_attributes in
    let* raw = parse_raw ~kind:discipline label.ld_attributes in
    let attribute =
      List.find label.ld_attributes ~f:(fun attribute ->
          Option.is_some (attribute_kind attribute))
    in
    let at =
      Option.value_map attribute ~default:label.ld_loc ~f:(fun attribute ->
          attribute.attr_loc)
    in
    match (discipline, label.ld_mutable, label.ld_atomic, boxed) with
    | discipline, Mutable, Nonatomic, true ->
        Ok
          (Some
             {
               record_path;
               position;
               label_id = label.ld_id;
               label = Ident.name label.ld_id;
               kind = Option.value discipline ~default:Ordinary;
               immutable = false;
               raw;
               value_type = label.ld_type;
               declared_at = label.ld_loc;
               at;
             })
    | None, Immutable, Nonatomic, true when heap ->
        Ok
          (Some
             {
               record_path;
               position;
               label_id = label.ld_id;
               label = Ident.name label.ld_id;
               kind = Ordinary;
               immutable = true;
               raw = false;
               value_type = label.ld_type;
               declared_at = label.ld_loc;
               at;
             })
    | None, _, _, _ -> Ok None
    | Some _, Immutable, _, _ -> error at "A field discipline requires a mutable field"
    | Some _, _, Atomic, _ -> error at "A field discipline requires a non-atomic field"
    | Some _, _, _, false -> error at "A field discipline requires a boxed record field"
  in
  let* fields = Result.all (List.mapi labels ~f:field) in
  Ok (List.filter_opt fields)

let of_declaration path declaration =
  let* fields =
    Result.all
      (List.map (records path declaration) ~f:(field_metadata ~canonicalize:Fn.id))
  in
  Ok (List.concat fields)

let check ~at ~expected ~actual =
  if Poly.equal expected.kind actual.kind && Bool.equal expected.raw actual.raw then Ok ()
  else
    error
      ~related:[ (expected.at, "The signature field"); (actual.at, "The actual field") ]
      at
      (Printf.sprintf "Field %s requires %s access, but the actual field uses %s access"
         expected.label
         (kind_name expected.kind ^ if expected.raw then " raw" else "")
         (kind_name actual.kind ^ if actual.raw then " raw" else ""))

type occurrence = Record of record_fields | Attribute of Parsetree.attribute

let rec signature_records owner signature =
  List.concat_map signature ~f:(function
    | Types.Sig_type (id, declaration, _, _) ->
        List.map (records (qualify owner id) declaration) ~f:(fun record -> Record record)
    | Sig_module (id, _, declaration, _, _) ->
        module_type_records (Some (qualify owner id)) declaration.md_type
    | Sig_modtype (id, declaration, _) ->
        Option.value_map declaration.mtd_type ~default:[]
          ~f:(module_type_records (Some (qualify owner id)))
    | Sig_value _ | Sig_typext _ | Sig_class _ | Sig_class_type _ -> [])

and module_type_records owner = function
  | Types.Mty_signature signature -> signature_records owner signature
  | Mty_functor (parameter, body) ->
      let parameters =
        match parameter with
        | Unit -> []
        | Named (id, parameter) ->
            module_type_records (Option.map id ~f:(fun id -> Path.Pident id)) parameter
      in
      parameters @ module_type_records owner body
  | Mty_ident _ | Mty_alias _ -> []

let collect ?owner ?(canonicalize = Fn.id) visit =
  (* The compiler iterator has unit callbacks. The accumulator stays local to this walk. *)
  let occurrences = ref [] in
  let add entries = occurrences := List.rev_append entries !occurrences in
  let base = Tast_iterator.default_iterator in
  let rec iterator owner : Tast_iterator.iterator =
    let module_owner id = Option.map id ~f:(qualify owner) in
    let parameter = function
      | Typedtree.Unit -> ()
      | Named (id, _, typ) ->
          let nested = iterator (Option.map id ~f:(fun id -> Path.Pident id)) in
          nested.module_type nested typ
    in
    {
      base with
      attribute =
        (fun self attribute ->
          if
            Option.is_some (attribute_kind attribute)
            || obsolete_attribute attribute
            || String.equal attribute.Parsetree.attr_name.txt "caravan.raw"
          then add [ Attribute attribute ];
          base.attribute self attribute);
      attributes = (fun self attributes -> List.iter attributes ~f:(self.attribute self));
      type_declaration =
        (fun self declaration ->
          add
            (List.map
               (records (qualify owner declaration.typ_id) declaration.typ_type)
               ~f:(fun record -> Record record));
          base.type_declaration self declaration);
      module_binding =
        (fun _ binding ->
          base.module_binding (iterator (module_owner binding.mb_id)) binding);
      module_declaration =
        (fun _ declaration ->
          base.module_declaration (iterator (module_owner declaration.md_id)) declaration);
      module_type_declaration =
        (fun _ declaration ->
          base.module_type_declaration
            (iterator (Some (qualify owner declaration.mtd_id)))
            declaration);
      module_expr =
        (fun self expression ->
          match expression.mod_desc with
          | Tmod_functor (formal, body) ->
              self.attributes self expression.mod_attributes;
              parameter formal;
              self.module_expr self body
          | _ -> base.module_expr self expression);
      module_type =
        (fun self typ ->
          match typ.mty_desc with
          | Tmty_functor (formal, body) ->
              self.attributes self typ.mty_attributes;
              parameter formal;
              self.module_type self body
          | _ -> base.module_type self typ);
      structure_item =
        (fun self item ->
          (match item.str_desc with
          | Tstr_include included -> add (signature_records owner included.incl_type)
          | _ -> ());
          base.structure_item self item);
      signature_item =
        (fun self item ->
          (match item.sig_desc with
          | Tsig_include included -> add (signature_records owner included.incl_type)
          | _ -> ());
          base.signature_item self item);
    }
  in
  visit (iterator owner);
  let records, attributes =
    List.partition_map (List.rev !occurrences) ~f:(function
      | Record record -> First record
      | Attribute attribute -> Second attribute)
  in
  let field_attributes =
    List.concat_map records ~f:(fun record ->
        List.concat_map record.labels ~f:(fun label -> label.Types.ld_attributes))
  in
  let* () =
    List.fold_result attributes ~init:() ~f:(fun () attribute ->
        let* () = check_spelling attribute in
        if
          List.exists field_attributes ~f:(fun allowed ->
              Poly.equal attribute.attr_loc allowed.Parsetree.attr_loc)
        then Ok ()
        else
          error attribute.attr_loc
            ("The [@" ^ attribute.attr_name.txt ^ "] attribute belongs on a record field"))
  in
  let* fields = Result.all (List.map records ~f:(field_metadata ~canonicalize)) in
  Ok (List.concat fields)

let collect_structure ?owner ?canonicalize structure =
  collect ?owner ?canonicalize (fun iterator -> iterator.structure iterator structure)

let collect_signature ?owner ?canonicalize signature =
  collect ?owner ?canonicalize (fun iterator -> iterator.signature iterator signature)
