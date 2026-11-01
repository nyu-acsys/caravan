(** OCaml's variant types as Raven data types. Raven declares a data type's constructors
    and destructors in the scope of the type, so each type gets a module of its own, named
    as the type, capitalized as Raven's type names are, with the type [T]. OCaml's lists
    and options are Raven's [List] and [Option], which Raven instantiates for their
    element types.

    A record type with a mutable field is a reference instead, with a Raven field per
    OCaml field, identified by its type and label; so is a ref cell, with a field per type
    of contents, as [ref_Int_contents]. A record type without a mutable field is a data
    type with one constructor, named as the type. *)

open Base
module R = Raven_api

let ( let* ) = Result.( >>= )
let loc (l : Location.t) = R.Loc.make l.loc_start l.loc_end

(** Length framing separates components even when a source name contains separators. *)
let framed components =
  Int.to_string (List.length components)
  ^ "$"
  ^ String.concat
      (List.map components ~f:(fun component ->
           Int.to_string (String.length component) ^ "$" ^ component))

let record_field_name record label = "record$" ^ framed [ record; label ]

type ctor = {
  ocaml : string;
  raven : string;  (** Uncapitalized, as Raven's constructors are. *)
  fields : string list;  (** The destructors of the arguments. *)
  args : Types.type_expr list;
}

type field = { label : string; raven_field : string; typ : Types.type_expr }
type collection_kind = Sequence | FinSet | Set | Map

type t = {
  id : Ident.t option;  (** [None] for Raven's [List] and [Option]. *)
  paths : Path.t list;  (** Other paths naming the same implementation type. *)
  module_name : string;
  module_path : string list option;
  cell_namespace : string list option;
  ctors : ctor list;
  heap : field list option;  (** The fields of a record type with a mutable field. *)
  alias : Types.type_expr option;  (** The type that an abbreviation stands for. *)
  collection : collection_kind option;
  mathematical_integer : bool;
  atomic_procedure : string option;
  backend_type : Qualified_name.t option;
  library : Path.t option;
      (** The path of an abstract type that a library declares, trusted: Raven's [T] of a
          module with no definition of it. *)
  at : Location.t;
}

let list =
  {
    id = None;
    paths = [];
    module_name = "List";
    ctors =
      [
        { ocaml = "[]"; raven = "nil"; fields = []; args = [] };
        { ocaml = "::"; raven = "::"; fields = [ "hd"; "tl" ]; args = [] };
      ];
    heap = None;
    alias = None;
    collection = None;
    mathematical_integer = false;
    atomic_procedure = None;
    backend_type = None;
    module_path = None;
    cell_namespace = None;
    library = None;
    at = Location.none;
  }

let option =
  {
    id = None;
    paths = [];
    module_name = "Option";
    ctors =
      [
        { ocaml = "None"; raven = "none"; fields = []; args = [] };
        { ocaml = "Some"; raven = "some"; fields = [ "value" ]; args = [] };
      ];
    heap = None;
    alias = None;
    collection = None;
    mathematical_integer = false;
    atomic_procedure = None;
    backend_type = None;
    module_path = None;
    cell_namespace = None;
    library = None;
    at = Location.none;
  }

(** The data type that [decl] declares, if it is a variant type. *)
let of_declaration (decl : Typedtree.type_declaration) : (t, Report.error) Result.t =
  let at = decl.typ_loc in
  match decl.typ_kind with
  | Ttype_variant cds when List.is_empty decl.typ_params ->
      let ctor (cd : Typedtree.constructor_declaration) =
        match cd.cd_args with
        | Cstr_tuple cts ->
            let raven = String.uncapitalize cd.cd_name.txt in
            Ok
              {
                ocaml = cd.cd_name.txt;
                raven;
                fields = List.mapi cts ~f:(fun i _ -> Printf.sprintf "%s_%d" raven i);
                args = List.map cts ~f:(fun (ct : Typedtree.core_type) -> ct.ctyp_type);
              }
        | Cstr_record _ -> Report.unsupported cd.cd_loc "A constructor with a record"
      in
      let* ctors = Result.all (List.map cds ~f:ctor) in
      Ok
        {
          id = Some decl.typ_id;
          paths = [];
          module_name = String.capitalize decl.typ_name.txt;
          ctors;
          heap = None;
          alias = None;
          collection = None;
          mathematical_integer = false;
          atomic_procedure = None;
          backend_type = None;
          module_path = None;
          cell_namespace = None;
          library = None;
          at;
        }
  | Ttype_record lds when List.is_empty decl.typ_params ->
      let name = decl.typ_name.txt in
      let labels =
        List.map lds ~f:(fun (ld : Typedtree.label_declaration) -> ld.ld_name.txt)
      in
      let types =
        List.map lds ~f:(fun (ld : Typedtree.label_declaration) ->
            match Types.get_desc ld.ld_type.ctyp_type with
            | Tpoly (t, []) -> t
            | _ -> ld.ld_type.ctyp_type)
      in
      let is_mutable (ld : Typedtree.label_declaration) =
        match ld.ld_mutable with Mutable -> true | Immutable -> false
      in
      let heap, ctors =
        if List.exists lds ~f:is_mutable then
          ( Some
              (List.map2_exn labels types ~f:(fun label typ ->
                   { label; raven_field = record_field_name name label; typ })),
            [] )
        else
          ( None,
            [
              {
                ocaml = "";
                raven = String.uncapitalize name;
                fields = labels;
                args = types;
              };
            ] )
      in
      Ok
        {
          id = Some decl.typ_id;
          paths = [];
          module_name = String.capitalize name;
          ctors;
          heap;
          alias = None;
          collection = None;
          mathematical_integer = false;
          atomic_procedure = None;
          backend_type = None;
          module_path = None;
          cell_namespace = None;
          library = None;
          at;
        }
  | Ttype_abstract when List.is_empty decl.typ_params && Option.is_some decl.typ_manifest
    ->
      Ok
        {
          id = Some decl.typ_id;
          paths = [];
          module_name = String.capitalize decl.typ_name.txt;
          ctors = [];
          heap = None;
          alias = Option.map decl.typ_manifest ~f:(fun ct -> ct.ctyp_type);
          collection = None;
          mathematical_integer = false;
          atomic_procedure = None;
          backend_type = None;
          module_path = None;
          cell_namespace = None;
          library = None;
          at;
        }
  | Ttype_variant _ | Ttype_record _ | Ttype_abstract ->
      Report.unsupported at "A type with parameters"
  | _ -> Report.unsupported at "This type definition"

(** Adds paths naming the same implementation type. *)
let with_paths (d : t) paths =
  let paths =
    List.fold paths ~init:d.paths ~f:(fun paths path ->
        if List.mem paths path ~equal:Path.same then paths else paths @ [ path ])
  in
  { d with paths }

(** Uses the allocated Raven name for the type and its record fields. *)
let with_name (d : t) module_name =
  let record_name = String.uncapitalize module_name in
  let ctors =
    List.map d.ctors ~f:(fun c ->
        if String.is_empty c.ocaml then { c with raven = record_name } else c)
  in
  let heap =
    Option.map d.heap ~f:(fun fields ->
        List.map fields ~f:(fun f ->
            { f with raven_field = record_field_name record_name f.label }))
  in
  { d with module_name; ctors; heap }

let declares (d : t) (p : Path.t) =
  (match (d.id, p) with Some id, Pident id' -> Ident.same id id' | _ -> false)
  || Option.exists d.library ~f:(Path.same p)
  || List.mem d.paths p ~equal:Path.same

(** The abstract type [name] of the library [library], the module with the identifier
    [library_id], declared at [at]. *)
let library_type ~library ~library_id ~at name =
  {
    id = None;
    paths = [];
    module_name = library ^ "_" ^ name;
    ctors = [];
    heap = None;
    alias = None;
    collection = None;
    mathematical_integer = false;
    atomic_procedure = None;
    backend_type = None;
    module_path = None;
    cell_namespace = None;
    library = Some (Path.Pdot (Pident library_id, name));
    at;
  }

(** A nominal proof resource, represented by the instantiated Raven module's type. *)
let resource_type ~name ~module_id ~at =
  { (library_type ~library:name ~library_id:module_id ~at "t") with module_name = name }

let parameter_type ~parameter ~name ~declaration ~backend =
  {
    (library_type ~library:"Parameter" ~library_id:parameter
       ~at:declaration.Typedtree.typ_loc name)
    with
    id = Some declaration.typ_id;
    backend_type = Some backend;
    alias = Option.map declaration.typ_manifest ~f:(fun t -> t.Typedtree.ctyp_type);
  }

(** A nominal proof token for an existing atomic procedure. *)
let atomic_token ~path ~procedure ~at =
  {
    list with
    id = None;
    module_name = procedure ^ "_token";
    ctors = [];
    library = Some path;
    atomic_procedure = Some procedure;
    at;
  }

(** A specification-only collection, declared as [id]. *)
let collection id kind =
  let module_name =
    match kind with Sequence -> "Seq" | FinSet -> "FinSet" | Set -> "Set" | Map -> "Map"
  in
  {
    id = Some id;
    paths = [];
    module_name;
    ctors = [];
    heap = None;
    alias = None;
    collection = Some kind;
    mathematical_integer = false;
    atomic_procedure = None;
    backend_type = None;
    module_path = None;
    cell_namespace = None;
    library = None;
    at = Location.none;
  }

(** The unbounded integer type of specifications. *)
let logical_integer id =
  {
    list with
    id = Some id;
    module_name = "Int";
    ctors = [];
    alias = Some Predef.type_int;
    mathematical_integer = true;
  }

let sequence id = collection id Sequence
let is_sequence (d : t) = match d.collection with Some Sequence -> true | _ -> false

(** The data type of the type constructor [p]: one of [types], a list or an option. *)
let find (types : t list) (p : Path.t) =
  if Path.same p Predef.path_list then Some list
  else if Path.same p Predef.path_option then Some option
  else List.find types ~f:(fun d -> declares d p)

let collection_kind types p = Option.bind (find types p) ~f:(fun d -> d.collection)

let is_collection types p kind =
  match (kind, collection_kind types p) with
  | Sequence, Some Sequence | FinSet, Some FinSet | Set, Some Set | Map, Some Map -> true
  | _ -> false

(** [t] with the abbreviations of [types] at its head expanded, and without the quantifier
    of a record label's type, which is not polymorphic here. *)
let rec expand (types : t list) (t : Types.type_expr) =
  match Types.get_desc t with
  | Tconstr (p, [], _) ->
      begin match find types p with
      | Some { alias = Some t; _ } -> expand types t
      | _ -> t
      end
  | Tpoly (t, []) -> expand types t
  | _ -> t

let desc types t = Types.get_desc (expand types t)

(** The backend constructor of [cstr], retaining its source payload types. *)
let find_cstr (types : t list) (cstr : Data_types.constructor_description) =
  match Types.get_desc cstr.cstr_res with
  | Tconstr (p, _, _) ->
      Option.bind (find types p) ~f:(fun d ->
          Option.map
            (List.find d.ctors ~f:(fun c -> String.equal c.ocaml cstr.cstr_name))
            ~f:(fun c ->
              let args = if Option.is_some d.id then cstr.cstr_args else c.args in
              (d, { c with args })))
  | _ -> None

(** Whether [p] is the path of [Stdlib.ref]. *)
let is_ref (p : Path.t) =
  match p with
  | Pdot (Pident m, "ref") -> String.equal (Ident.name m) "Stdlib"
  | _ -> false

(** Whether [p] is the path of [Stdlib.Atomic.t]. *)
let is_atomic (p : Path.t) =
  match Path.name p with "Stdlib.Atomic.t" | "Stdlib__Atomic.t" -> true | _ -> false

(** The opaque reference type used for proof-only storage. *)
let is_ghost (p : Path.t) = String.equal (Path.name p) "Ghost.t"

(** The fractional permission type of specifications. *)
let is_permission (p : Path.t) = String.equal (Path.name p) "Permission.t"

(** Whether [t] itself is a heap reference, rather than a value containing one. *)
let is_heap_ref (types : t list) (t : Types.type_expr) =
  match desc types t with
  | Tconstr (p, [ _ ], _) when is_ref p || is_atomic p -> true
  | Tconstr (p, [], _) when is_ghost p -> true
  | Tconstr (p, [], _) -> Option.exists (find types p) ~f:(fun d -> Option.is_some d.heap)
  | _ -> false

(** Owners of generic data layouts retained in a value's Raven type. *)
let cell_namespaces (data : t list) (typ : Types.type_expr) =
  let rec collect typ =
    match desc data typ with
    | Tconstr (path, [ _ ], _) when is_ref path || is_atomic path -> []
    | Tconstr (path, [ element ], _)
      when Path.same path Predef.path_list || Path.same path Predef.path_option ->
        collect element
    | Tconstr (path, arguments, _) when Option.is_some (collection_kind data path) ->
        List.concat_map arguments ~f:collect
    | Tconstr (path, [], _) ->
        begin match find data path with
        | Some { heap = None; cell_namespace = Some owner; _ } -> [ owner ]
        | Some _ | None -> []
        end
    | Ttuple components ->
        List.concat_map components ~f:(fun (_, element) -> collect element)
    | _ -> []
  in
  List.fold (collect typ) ~init:[] ~f:(fun owners owner ->
      if List.mem owners owner ~equal:(List.equal String.equal) then owners
      else owners @ [ owner ])

(** The data type and constructor named [ocaml] in a contract: the latest such
    constructor, as in OCaml, where those of lists and options come first. *)
let find_ctor (types : t list) (ocaml : string) =
  List.find_map
    (List.rev (list :: option :: types))
    ~f:(fun d ->
      Option.map
        (List.find d.ctors ~f:(fun c -> String.equal c.ocaml ocaml))
        ~f:(fun c -> (d, c)))

let ctor_name ~loc:l (d : t) (c : ctor) =
  R.Name.make ~loc:l ~path:(Option.value d.module_path ~default:[ d.module_name ]) c.raven

(** The Raven type of the OCaml type [t]; [self] is the data type being defined, if any,
    which its module calls [T]. *)
let rec typ (types : t list) ?self ~(at : Location.t) (t : Types.type_expr) :
    (R.Type.t, Report.error) Result.t =
  let l = loc at in
  match desc types t with
  | Tconstr (p, [], _) when Path.same p Predef.path_int -> Ok (R.Type.int ~loc:l)
  | Tconstr (p, [], _) when Path.same p Predef.path_bool -> Ok (R.Type.bool ~loc:l)
  | Tconstr (p, [], _) when Path.same p Predef.path_unit -> Ok (R.Type.tuple ~loc:l [])
  | Tconstr (p, [], _) when is_ghost p -> Ok (R.Type.ref ~loc:l)
  | Tconstr (p, [], _) when is_permission p -> Ok (R.Type.real ~loc:l)
  | Tconstr (p, [ elt ], _)
    when Path.same p Predef.path_list || Path.same p Predef.path_option ->
      let* elt = typ types ?self ~at elt in
      let d = Option.value_exn (find types p) in
      Ok (R.Type.named ~loc:l (R.Name.make ~loc:l d.module_name) [ elt ])
  | Tconstr (p, [ _ ], _) when is_ref p || is_atomic p -> Ok (R.Type.ref ~loc:l)
  | Tconstr (p, [ elt ], _) when Option.exists (find types p) ~f:is_sequence ->
      let* elt = typ types ?self ~at elt in
      Ok (R.Type.named ~loc:l (R.Name.make ~loc:l "Seq") [ elt ])
  | Tconstr (p, [ elt ], _) when is_collection types p FinSet ->
      let* elt = typ types ?self ~at elt in
      Ok (R.Type.fin_set ~loc:l elt)
  | Tconstr (p, [ elt ], _) when is_collection types p Set ->
      let* elt = typ types ?self ~at elt in
      Ok (R.Type.set ~loc:l elt)
  | Tconstr (p, [ key; value ], _) when is_collection types p Map ->
      let* key = typ types ?self ~at key in
      let* value = typ types ?self ~at value in
      Ok (R.Type.map ~loc:l key value)
  | Tconstr (p, [], _)
    when Option.exists (find types p) ~f:(fun d -> Option.is_some d.heap) ->
      Ok (R.Type.ref ~loc:l)
  | Tconstr (p, [], _) when Option.exists self ~f:(fun d -> declares d p) ->
      Ok (R.Type.named ~loc:l (R.Name.make ~loc:l "T") [])
  | Tconstr (p, [], _)
    when Option.exists (find types p) ~f:(fun d -> Option.is_some d.backend_type) ->
      let d = Option.value_exn (find types p) in
      Ok
        (R.Type.named ~loc:l
           (Qualified_name.raven ~loc:l (Option.value_exn d.backend_type))
           [])
  | Tconstr (p, [], _)
    when Option.exists (find types p) ~f:(fun d -> Option.is_some d.atomic_procedure) ->
      let d = Option.value_exn (find types p) in
      Ok
        (R.Type.atomic_token ~loc:l
           (Qualified_name.raven ~loc:l
              (Qualified_name.of_string (Option.value_exn d.atomic_procedure))))
  | Tconstr (p, [], _) when List.exists types ~f:(fun d -> declares d p) ->
      let d = Option.value_exn (find types p) in
      Ok (R.Type.named ~loc:l (R.Name.make ~loc:l ~path:[ d.module_name ] "T") [])
  | Ttuple components ->
      let* components =
        Result.all (List.map components ~f:(fun (_, t) -> typ types ?self ~at t))
      in
      Ok (R.Type.tuple ~loc:l components)
  (* The type of a record label, which is not polymorphic here. *)
  | Tpoly (t, []) -> typ types ?self ~at t
  | _ -> Report.unsupported at (Stdlib.Format.asprintf "The type %a" Printtyp.type_expr t)

(** Storage identities use the translated type structure, rather than a display tag.
    References have one representation; nominal value types retain their owner. *)
type type_key =
  | Int_key
  | Integer_key
  | Bool_key
  | Unit_key
  | Ref_key
  | Permission_key
  | Named_key of string list
  | List_key of type_key
  | Option_key of type_key
  | Seq_key of type_key
  | Finset_key of type_key
  | Set_key of type_key
  | Map_key of type_key * type_key
  | Tuple_key of type_key list
  | Atomic_token_key of string list

let equal_type_key = Poly.equal

let rec type_key types t =
  let mathematical =
    match Types.get_desc t with
    | Tconstr (path, [], _) ->
        Option.exists (find types path) ~f:(fun data -> data.mathematical_integer)
    | _ -> false
  in
  let unary constructor element = Option.map (type_key types element) ~f:constructor in
  let alias =
    match Types.get_desc t with
    | Tconstr (path, [], _) -> Option.bind (find types path) ~f:(fun data -> data.alias)
    | Tpoly (body, []) -> Some body
    | _ -> None
  in
  if mathematical then Some Integer_key
  else if Option.is_some alias then type_key types (Option.value_exn alias)
  else
    match desc types t with
    | Tconstr (p, [], _) when Path.same p Predef.path_int -> Some Int_key
    | Tconstr (p, [], _) when Path.same p Predef.path_bool -> Some Bool_key
    | Tconstr (p, [], _) when Path.same p Predef.path_unit -> Some Unit_key
    | Tconstr (p, [], _) when is_permission p -> Some Permission_key
    | Tconstr (p, [], _) when is_ghost p -> Some Ref_key
    | Tconstr (p, [ _ ], _) when is_ref p || is_atomic p -> Some Ref_key
    | Tconstr (p, [ element ], _) when Path.same p Predef.path_list ->
        unary (fun key -> List_key key) element
    | Tconstr (p, [ element ], _) when Path.same p Predef.path_option ->
        unary (fun key -> Option_key key) element
    | Tconstr (p, arguments, _) when Option.is_some (collection_kind types p) ->
        begin match (collection_kind types p, arguments) with
        | Some Sequence, [ element ] -> unary (fun key -> Seq_key key) element
        | Some FinSet, [ element ] -> unary (fun key -> Finset_key key) element
        | Some Set, [ element ] -> unary (fun key -> Set_key key) element
        | Some Map, [ key; value ] ->
            Option.map
              (Option.both (type_key types key) (type_key types value))
              ~f:(fun (key, value) -> Map_key (key, value))
        | _ -> None
        end
    | Tconstr (p, [], _) ->
        Option.map (find types p) ~f:(fun data ->
            match (data.heap, data.atomic_procedure, data.backend_type) with
            | Some _, _, _ -> Ref_key
            | None, Some operation, _ -> Atomic_token_key (String.split operation ~on:'.')
            | None, None, Some qualified ->
                Named_key (qualified.Qualified_name.path @ [ qualified.name ])
            | None, None, None -> Named_key [ data.module_name; "T" ])
    | Ttuple components ->
        Option.map
          (Option.all (List.map components ~f:(fun (_, t) -> type_key types t)))
          ~f:(fun keys -> Tuple_key keys)
    | Tpoly (body, []) -> type_key types body
    | _ -> None

let rec key_name = function
  | Int_key -> "Int"
  | Integer_key -> "Integer"
  | Bool_key -> "Bool"
  | Unit_key -> "Unit"
  | Ref_key -> "Ref"
  | Permission_key -> "Permission"
  | Named_key path -> "Named$" ^ framed path
  | List_key child -> key_name child ^ "List"
  | Option_key child -> key_name child ^ "Option"
  | Seq_key child -> key_name child ^ "Seq"
  | Finset_key child -> key_name child ^ "FinSet"
  | Set_key child -> key_name child ^ "Set"
  | Map_key (key, value) -> "Map$" ^ framed [ key_name key; key_name value ]
  | Tuple_key arguments -> "Tuple$" ^ framed (List.map arguments ~f:key_name)
  | Atomic_token_key path -> "Token$" ^ framed [ key_name (Named_key path) ]

let relative_path owner path =
  let rec strip owner path =
    match (owner, path) with
    | [], rest -> Some rest
    | prefix :: owner, component :: path when String.equal prefix component ->
        strip owner path
    | _ -> None
  in
  Option.value (strip owner path) ~default:path

let rec relative_key owner = function
  | (Int_key | Integer_key | Bool_key | Unit_key | Ref_key | Permission_key) as key -> key
  | Named_key path -> Named_key (relative_path owner path)
  | List_key child -> List_key (relative_key owner child)
  | Option_key child -> Option_key (relative_key owner child)
  | Seq_key child -> Seq_key (relative_key owner child)
  | Finset_key child -> Finset_key (relative_key owner child)
  | Set_key child -> Set_key (relative_key owner child)
  | Map_key (key, value) -> Map_key (relative_key owner key, relative_key owner value)
  | Tuple_key arguments -> Tuple_key (List.map arguments ~f:(relative_key owner))
  | Atomic_token_key path -> Atomic_token_key (relative_path owner path)

type cell_key = {
  namespace : string list;
  prefix : string;
  suffix : string;
  payload : type_key;
}

let equal_cell_key = Poly.equal

let cell_identity ~prefix ~suffix data typ =
  let namespace =
    match cell_namespaces data typ with
    | [] -> Some []
    | [ owner ] -> Some owner
    | owners when List.for_all owners ~f:(fun owner -> List.length owner = 1) -> Some []
    | _ -> None
  in
  Option.bind namespace ~f:(fun namespace ->
      Option.map (type_key data typ) ~f:(fun payload ->
          { namespace; prefix; suffix; payload = relative_key namespace payload }))

let cell_key_name key =
  String.concat ~sep:"."
    (key.namespace @ [ key.prefix ^ key_name key.payload ^ key.suffix ])

let cell_name ~prefix ~suffix data typ =
  Option.map (cell_identity ~prefix ~suffix data typ) ~f:cell_key_name

let rec is_int types t =
  match Types.get_desc t with
  | Tconstr (p, [], _) ->
      begin match find types p with
      | Some { mathematical_integer = true; _ } -> false
      | Some { alias = Some t; _ } -> is_int types t
      | _ -> Path.same p Predef.path_int
      end
  | Tpoly (t, []) -> is_int types t
  | _ -> false

(** The field [name] of type [typ], for values of the OCaml type [t]: an [int] field's
    values are in [int]'s range, which owning the field then implies. *)
let field_member ?(ghost = false) types ~loc name typ (t : Types.type_expr) =
  let where = Option.some_if (is_int types t) (R.Name.make ~loc Prelude.in_range) in
  R.Member.field ~loc ~ghost ?where (R.Ident.make ~loc name) typ

(** Whether the values of type [t] are immediate or references, so that physical equality
    on them is equality: integers, booleans, unit, references, and variants whose
    constructors are all constant. *)
let rec immediate (types : t list) (t : Types.type_expr) =
  match desc types t with
  | Tconstr (p, [], _)
    when Path.same p Predef.path_int || Path.same p Predef.path_bool
         || Path.same p Predef.path_unit ->
      true
  | Tconstr (p, [ _ ], _) when is_ref p || is_atomic p -> true
  | Tconstr (p, [], _) when is_ghost p -> true
  | Tconstr (p, [], _) ->
      begin match find types p with
      | Some { heap = Some _; _ } -> true
      | Some { ctors = _ :: _ as ctors; _ } ->
          List.for_all ctors ~f:(fun c -> List.is_empty c.args)
      | _ -> false
      end
  | Tpoly (t, []) -> immediate types t
  | _ -> false

(** Whether values of type [t] may contain references. *)
let has_refs (types : t list) (t : Types.type_expr) =
  let rec go seen t =
    match desc types t with
    | Tconstr (p, [ _ ], _) when is_ref p || is_atomic p -> true
    | Tconstr (p, [], _) when is_ghost p -> true
    | Tconstr (p, args, _) -> begin
        List.exists args ~f:(go seen)
        ||
        match find types p with
        | Some { heap = Some _; _ } -> true
        | Some { library = Some _; _ } -> true
        | Some d when not (List.mem seen p ~equal:Path.same) ->
            List.exists d.ctors ~f:(fun c -> List.exists c.args ~f:(go (p :: seen)))
        | _ -> false
      end
    | Ttuple components -> List.exists components ~f:(fun (_, t) -> go seen t)
    | Tpoly (t, []) -> go seen t
    | _ -> false
  in
  go [] t

(** The field of the record type of [label], and whether its record is a reference. *)
let find_label (types : t list) (label : Data_types.label_description) =
  match Types.get_desc label.lbl_res with
  | Tconstr (p, _, _) -> Option.map (find types p) ~f:(fun d -> d)
  | _ -> None

(** The fields declaring the fields of the record types of [types] that are references. *)
let fields ?declarations (types : t list) : (R.Member.t list, Report.error) Result.t =
  let field (d : t) (f : field) =
    let* typ = typ types ~at:d.at f.typ in
    let l = loc d.at in
    Ok (field_member types ~loc:l f.raven_field typ f.typ)
  in
  Result.all
    (List.concat_map (Option.value declarations ~default:types) ~f:(fun d ->
         List.map (Option.value d.heap ~default:[]) ~f:(field d)))

(** The module declaring [d], given the data types declared before it. *)
let member (types : t list) (d : t) : (R.Member.t, Report.error) Result.t =
  let l = loc d.at in
  let variant (c : ctor) =
    let* args =
      Result.all
        (List.map2_exn c.fields c.args ~f:(fun field t ->
             let* t = typ types ~self:d ~at:d.at t in
             Ok (R.Ident.make ~loc:l field, t)))
    in
    Ok (R.Type.variant ~loc:l (R.Ident.make ~loc:l c.raven) args)
  in
  let* variants = Result.all (List.map d.ctors ~f:variant) in
  let t =
    match d.library with
    | Some _ -> R.Member.free (R.Member.type_ ~loc:l (R.Ident.make ~loc:l "T") None)
    | None ->
        R.Member.type_ ~loc:l (R.Ident.make ~loc:l "T")
          (Some (R.Type.data ~loc:l variants))
  in
  Ok (R.Member.module_ ~loc:l (R.Ident.make ~loc:l d.module_name) [ t ])
