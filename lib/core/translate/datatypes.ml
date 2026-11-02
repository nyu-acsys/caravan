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
  variable : Types.type_expr option;  (** A scheme-local source type variable binding. *)
  module_name : string;
  module_path : string list option;
  cell_namespace : string list option;
  ctors : ctor list;
  heap : field list option;  (** The fields of a record type with a mutable field. *)
  alias : Types.type_expr option;  (** The type that an abbreviation stands for. *)
  collection : collection_kind option;
  mathematical_integer : bool;
  mathematical : bool;
      (** A logical model whose carrier is not a runtime value domain. *)
  empty : bool;  (** An empty source variant, represented by an inhabited carrier. *)
  value_constraint : Qualified_name.t option;
      (** An abstract source-value domain, distinct from mathematical carrier validity. *)
  domain_scope : string list option;
      (** The lexical scope containing parameters used by this value representation. *)
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
    variable = None;
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
    mathematical = false;
    empty = false;
    value_constraint = None;
    domain_scope = None;
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
    variable = None;
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
    mathematical = false;
    empty = false;
    value_constraint = None;
    domain_scope = None;
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
          variable = None;
          module_name = String.capitalize decl.typ_name.txt;
          ctors;
          heap = None;
          alias = None;
          collection = None;
          mathematical_integer = false;
          mathematical = false;
          empty = List.is_empty cds;
          value_constraint = None;
          domain_scope = None;
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
          variable = None;
          module_name = String.capitalize name;
          ctors;
          heap;
          alias = None;
          collection = None;
          mathematical_integer = false;
          mathematical = false;
          empty = false;
          value_constraint = None;
          domain_scope = None;
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
          variable = None;
          module_name = String.capitalize decl.typ_name.txt;
          ctors = [];
          heap = None;
          alias = Option.map decl.typ_manifest ~f:(fun ct -> ct.ctyp_type);
          collection = None;
          mathematical_integer = false;
          mathematical = false;
          empty = false;
          value_constraint = None;
          domain_scope = None;
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
  let value_constraint =
    Option.map d.value_constraint ~f:(fun constraint_ ->
        if List.equal String.equal constraint_.Qualified_name.path [ d.module_name ] then
          { constraint_ with path = [ module_name ] }
        else constraint_)
  in
  { d with module_name; ctors; heap; value_constraint }

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
    variable = None;
    module_name = library ^ "_" ^ name;
    ctors = [];
    heap = None;
    alias = None;
    collection = None;
    mathematical_integer = false;
    mathematical = false;
    empty = false;
    value_constraint = None;
    domain_scope = None;
    atomic_procedure = None;
    backend_type = None;
    module_path = None;
    cell_namespace = None;
    library = Some (Path.Pdot (Pident library_id, name));
    at;
  }

(** Keeps a logical datatype's mathematical carrier unrestricted. *)
let with_mathematical_domain (d : t) = { d with mathematical = true }

(** Gives an imported runtime type its unknown source-value domain. *)
let with_abstract_domain (d : t) =
  {
    d with
    value_constraint =
      Some Qualified_name.{ path = [ d.module_name ]; name = "ocaml_value" };
  }

(** A nominal proof resource, represented by the instantiated Raven module's type. *)
let resource_type ~name ~module_id ~at =
  { (library_type ~library:name ~library_id:module_id ~at "t") with module_name = name }

(** Binds a generalized variable directly to its worker's value dictionary. *)
let variable_type ~variable ~owner ~parameter ~at =
  let path = owner @ [ parameter ] in
  {
    list with
    variable = Some variable;
    module_name = parameter;
    module_path = Some path;
    ctors = [];
    backend_type = Some Qualified_name.{ path; name = "Carrier" };
    value_constraint = Some Qualified_name.{ path; name = "holds" };
    domain_scope = Some owner;
    at;
  }

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
    variable = None;
    module_name;
    ctors = [];
    heap = None;
    alias = None;
    collection = Some kind;
    mathematical_integer = false;
    mathematical = false;
    empty = false;
    value_constraint = None;
    domain_scope = None;
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

(** Variable IDs are local to the typed binding and never become generated names. *)
let find_variable (types : t list) variable =
  let variable = expand types variable in
  match Types.get_desc variable with
  | Tvar _ ->
      List.find types ~f:(fun data ->
          Option.exists data.variable ~f:(fun bound ->
              Int.equal (Types.get_id (expand types bound)) (Types.get_id variable)))
  | _ -> None

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
  | Tvar _ ->
      begin match
        Option.bind (find_variable types t) ~f:(fun data -> data.backend_type)
      with
      | Some backend -> Ok (R.Type.named ~loc:l (Qualified_name.raven ~loc:l backend) [])
      | None -> Report.unsupported at "An unbound polymorphic type variable"
      end
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
    | Tvar _ ->
        Option.map
          (Option.bind (find_variable types t) ~f:(fun data -> data.backend_type))
          ~f:(fun backend -> Named_key (backend.Qualified_name.path @ [ backend.name ]))
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
      | Some { mathematical_integer = true; _ } | Some { mathematical = true; _ } -> false
      | Some { alias = Some t; _ } -> is_int types t
      | _ -> Path.same p Predef.path_int
      end
  | Tpoly (t, []) -> is_int types t
  | _ -> false

let rec abstract_value_constraint types t =
  match Types.get_desc t with
  | Tvar _ -> Option.bind (find_variable types t) ~f:(fun data -> data.value_constraint)
  | Tconstr (path, [], _) ->
      begin match find types path with
      | Some { mathematical = true; _ } -> None
      | Some { value_constraint = Some constraint_; _ } -> Some constraint_
      | Some { alias = Some body; _ } -> abstract_value_constraint types body
      | Some _ | None -> None
      end
  | Tpoly (body, []) -> abstract_value_constraint types body
  | _ -> None

(** Whether the carrier contains values outside the source value domain. Recursive
    algebraic cycles without constrained payloads have a trivial domain. *)
let has_domain types t =
  let rec visit seen t =
    let mathematical =
      match Types.get_desc t with
      | Tconstr (path, [], _) ->
          Option.exists (find types path) ~f:(fun d -> d.mathematical)
      | _ -> false
    in
    if mathematical then false
    else if Option.is_some (abstract_value_constraint types t) || is_int types t then true
    else
      match Types.get_desc t with
      | Tconstr (path, [], _) ->
          begin match find types path with
          | Some { mathematical_integer = true; _ } -> false
          | Some { alias = Some body; _ } -> visit seen body
          | Some { heap = Some _; _ } | Some { library = Some _; _ } -> false
          | Some data when data.empty -> true
          | Some data when not (List.mem seen path ~equal:Path.same) ->
              List.exists data.ctors ~f:(fun ctor ->
                  List.exists ctor.args ~f:(visit (path :: seen)))
          | Some _ | None -> false
          end
      | Tconstr (path, [ element ], _)
        when Path.same path Predef.path_list || Path.same path Predef.path_option ->
          visit seen element
      | Ttuple components -> List.exists components ~f:(fun (_, t) -> visit seen t)
      | Tpoly (body, []) -> visit seen body
      | _ -> false
  in
  visit [] t

(** A container domain must be declared where all of its carrier parameters are visible.
    Layout-dependent carriers retain the layout's own domain members. *)
let domain_identity types t =
  let rec scopes seen t =
    match Types.get_desc t with
    | Tvar _ ->
        Option.value_map (find_variable types t) ~default:[] ~f:(fun data ->
            Option.to_list data.domain_scope)
    | Tconstr (path, [ _ ], _) when is_ref path || is_atomic path -> []
    | Tconstr (path, [], _) ->
        begin match find types path with
        | Some { heap = Some _; _ } -> []
        | Some data ->
            let own = Option.to_list data.domain_scope in
            begin match data.alias with
            | Some body ->
                (if Option.is_some data.value_constraint then own else [])
                @ scopes seen body
            | None when data.mathematical -> own
            | None when not (List.mem seen path ~equal:Path.same) ->
                own
                @ List.concat_map data.ctors ~f:(fun ctor ->
                    List.concat_map ctor.args ~f:(scopes (path :: seen)))
            | None -> own
            end
        | None -> []
        end
    | Tconstr (path, [ element ], _)
      when Path.same path Predef.path_list || Path.same path Predef.path_option ->
        scopes seen element
    | Ttuple components -> List.concat_map components ~f:(fun (_, t) -> scopes seen t)
    | Tpoly (body, []) -> scopes seen body
    | _ -> []
  in
  let prefix outer inner = List.is_prefix inner ~prefix:outer ~equal:String.equal in
  let merge scope next =
    if prefix scope next then Some next
    else if prefix next scope then Some scope
    else None
  in
  Option.bind (cell_identity ~prefix:"ocaml_value$" ~suffix:"" types t) ~f:(fun key ->
      if not (List.is_empty key.namespace) then Some key
      else
        Option.map
          (List.fold (scopes [] t) ~init:(Some []) ~f:(fun scope next ->
               Option.bind scope ~f:(fun scope -> merge scope next)))
          ~f:(fun namespace ->
            { key with namespace; payload = relative_key namespace key.payload }))

let container types t =
  match desc types t with
  | Tconstr (path, [ _ ], _)
    when Path.same path Predef.path_list || Path.same path Predef.path_option ->
      true
  | Ttuple _ -> true
  | _ -> false

let structural_constraint_name types t =
  match domain_identity types t with
  | Some key -> Some (cell_key_name key)
  | None -> Option.map (type_key types t) ~f:(fun key -> "ocaml_value$" ^ key_name key)

let supplied_dictionary types t =
  match abstract_value_constraint types t with
  | Some { Qualified_name.path; name = "holds" } ->
      Option.some_if (not (List.is_empty path)) (String.concat ~sep:"." path)
  | Some _ | None -> None

let rec domain_key ~namespace types t =
  match abstract_value_constraint types t with
  | Some predicate ->
      let parts = predicate.Qualified_name.path @ [ predicate.name ] in
      let parts =
        if List.is_prefix parts ~prefix:namespace ~equal:String.equal then
          List.drop parts (List.length namespace)
        else parts
      in
      "abstract$" ^ framed parts
  | None when is_int types t -> "bounded_int"
  | None when not (has_domain types t) -> "unrestricted"
  | None -> (
      match desc types t with
      | Tconstr (path, [ element ], _) when Path.same path Predef.path_list ->
          "list$" ^ framed [ domain_key ~namespace types element ]
      | Tconstr (path, [ element ], _) when Path.same path Predef.path_option ->
          "option$" ^ framed [ domain_key ~namespace types element ]
      | Ttuple components ->
          "tuple$"
          ^ framed (List.map components ~f:(fun (_, t) -> domain_key ~namespace types t))
      | _ ->
          "nominal$"
          ^ framed
              (Option.value_map (structural_constraint_name types t) ~default:[]
                 ~f:(fun name ->
                   let parts = String.split name ~on:'.' in
                   if List.is_prefix parts ~prefix:namespace ~equal:String.equal then
                     List.drop parts (List.length namespace)
                   else parts)))

let dictionary_name types t =
  match supplied_dictionary types t with
  | Some dictionary -> Some dictionary
  | None when is_int types t -> Some Prelude.value_int
  | None ->
      Option.map (domain_identity types t) ~f:(fun key ->
          String.concat ~sep:"."
            (key.namespace
            @ [
                "Ocaml$Values$"
                ^ framed
                    [ key_name key.payload; domain_key ~namespace:key.namespace types t ];
              ]))

let constraint_name types t =
  match abstract_value_constraint types t with
  | Some constraint_ -> Some (Qualified_name.to_string constraint_)
  | None when is_int types t -> Some Prelude.in_range
  | None when not (has_domain types t) -> None
  | None when container types t ->
      Option.map (dictionary_name types t) ~f:(fun dictionary -> dictionary ^ ".holds")
  | None -> structural_constraint_name types t

let domain_namespace types t =
  Option.map (domain_identity types t) ~f:(fun key -> key.namespace)

let unique_domain_members members =
  let _, members =
    List.fold members
      ~init:(Set.empty (module String), [])
      ~f:(fun (seen, members) ((name, _) as member) ->
        if Set.mem seen name then (seen, members)
        else (Set.add seen name, member :: members))
  in
  List.rev members

let admissible ~loc types t value =
  Option.map (constraint_name types t) ~f:(fun name ->
      R.Expr.call ~loc
        (Qualified_name.raven ~loc (Qualified_name.of_string name))
        [ value ])

type domain_node =
  | Domain_function of Types.type_expr * string
  | Value_dictionary of Types.type_expr * string option

(** Plans declarations and template requirements with one dependency traversal. *)
let domain_nodes ?(dictionaries = false) types requested =
  let children t =
    match desc types t with
    | Tconstr (path, [ element ], _)
      when Path.same path Predef.path_list || Path.same path Predef.path_option ->
        [ element ]
    | Tconstr (path, [], _) ->
        Option.value_map (find types path) ~default:[] ~f:(fun data ->
            List.concat_map data.ctors ~f:(fun ctor -> ctor.args))
    | Ttuple components -> List.map components ~f:snd
    | _ -> []
  in
  let rec domain (seen, nodes) t =
    match constraint_name types t with
    | _ when Option.is_some (abstract_value_constraint types t) -> (seen, nodes)
    | None -> (seen, nodes)
    | Some name when String.equal name Prelude.in_range || Set.mem seen name ->
        (seen, nodes)
    | Some _ when container types t -> dictionary (seen, nodes) t
    | Some name ->
        let seen, nodes =
          List.fold (children t) ~init:(Set.add seen name, nodes) ~f:domain
        in
        (seen, Domain_function (t, name) :: nodes)
  and dictionary (seen, nodes) t =
    match (supplied_dictionary types t, dictionary_name types t) with
    | Some _, _ -> (seen, nodes)
    | None, None -> (seen, Value_dictionary (t, None) :: nodes)
    | None, Some name when Set.mem seen name -> (seen, nodes)
    | None, Some name ->
        let seen = Set.add seen name in
        if String.equal name Prelude.value_int then
          (seen, Value_dictionary (t, Some name) :: nodes)
        else if container types t then
          let seen, nodes = List.fold (children t) ~init:(seen, nodes) ~f:dictionary in
          (seen, Value_dictionary (t, Some name) :: nodes)
        else
          (* A nominal dictionary supplies the carrier of its recursive containers. *)
          domain (seen, Value_dictionary (t, Some name) :: nodes) t
  in
  let _, nodes =
    List.fold requested
      ~init:(Set.empty (module String), [])
      ~f:(if dictionaries then dictionary else domain)
  in
  List.rev nodes

(** The monomorphic domain functions needed by the requested carriers. Mathematical
    collections and abstract library carriers retain their own logical contracts. *)
let domain_members ?(dictionaries = false) types requested =
  let conjunction ~loc expressions =
    Option.value
      (List.reduce expressions ~f:(R.Expr.binary ~loc And))
      ~default:(R.Expr.bool ~loc true)
  in
  let definition t qualified =
    let at =
      match desc types t with
      | Tconstr (path, [], _) ->
          Option.value_map (find types path) ~default:Location.none ~f:(fun d -> d.at)
      | _ -> Location.none
    in
    let l = loc at in
    let ident text = R.Ident.make ~loc:l text in
    let value text = R.Expr.var ~loc:l (R.Name.make ~loc:l text) in
    let x = value "source$value" in
    let holds t expression = admissible ~loc:l types t expression in
    let conjuncts terms = conjunction ~loc:l (List.filter_opt terms) in
    let datatype_cases ctors =
      List.map ctors ~f:(fun ctor ->
          let arguments = List.mapi ctor.args ~f:(fun i _ -> "part$" ^ Int.to_string i) in
          ( R.Expr.Case (ident ctor.raven, List.map arguments ~f:ident),
            conjuncts
              (List.map2_exn ctor.args arguments ~f:(fun t name -> holds t (value name)))
          ))
    in
    let body =
      match desc types t with
      | Tconstr (path, [], _) ->
          begin match find types path with
          | Some data when data.empty -> R.Expr.bool ~loc:l false
          | Some data -> R.Expr.match_ ~loc:l x (datatype_cases data.ctors)
          | None -> R.Expr.bool ~loc:l true
          end
      | _ -> R.Expr.bool ~loc:l true
    in
    let* carrier = typ types ~at t in
    let name = Qualified_name.of_string qualified in
    Ok
      (R.Member.callable
         (R.Callable.func ~loc:l
            ~formals:[ R.Var.make ~loc:l (ident "source$value") carrier ]
            ~returns:
              [ R.Var.make ~loc:l (ident "source$admissible") (R.Type.bool ~loc:l) ]
            (ident name.name) (Some body)))
  in
  let dictionary_definition t qualified =
    let l = loc Location.none in
    let q text = Qualified_name.raven ~loc:l (Qualified_name.of_string text) in
    let ident text = R.Ident.make ~loc:l text in
    let module_arg t =
      match dictionary_name types t with
      | Some dictionary -> Ok (R.Type.named ~loc:l (q dictionary) [])
      | None -> Report.unsupported Location.none "This value dictionary's carrier"
    in
    let* factory, arguments =
      match desc types t with
      | Tconstr (path, [ element ], _) when Path.same path Predef.path_list ->
          let* argument = module_arg element in
          Ok (Some Prelude.value_list, [ argument ])
      | Tconstr (path, [ element ], _) when Path.same path Predef.path_option ->
          let* argument = module_arg element in
          Ok (Some Prelude.value_option, [ argument ])
      | Ttuple components ->
          let* arguments =
            Result.all (List.map components ~f:(fun (_, t) -> module_arg t))
          in
          Ok (Some (Prelude.value_tuple (List.length components)), arguments)
      | _ -> Ok (None, [])
    in
    let name = Qualified_name.of_string qualified in
    match factory with
    | Some factory ->
        Ok
          (R.Member.instance ~loc:l
             ~def:(q factory, arguments)
             (ident name.name) (q factory))
    | None ->
        let* carrier = typ types ~at:Location.none t in
        let value = R.Expr.var ~loc:l (R.Name.make ~loc:l "value") in
        let body =
          Option.value
            (admissible ~loc:l types t value)
            ~default:(R.Expr.bool ~loc:l true)
        in
        Ok
          (Prelude.value_dictionary ~loc:l ~name:name.name ~carrier
             ~unrestricted:(R.Expr.bool ~loc:l (not (has_domain types t)))
             ~body)
  in
  let require_identity t =
    match domain_identity types t with
    | Some identity -> Ok identity
    | None ->
        Report.unsupported Location.none
          "A source value domain combining incompatible symbolic scopes"
  in
  let* members =
    Result.all
      (List.map (domain_nodes ~dictionaries types requested) ~f:(function
        | Value_dictionary (_, None) ->
            Report.unsupported Location.none "This source value dictionary"
        | Value_dictionary (_, Some name) when String.equal name Prelude.value_int ->
            Ok None
        | Value_dictionary (t, Some name) ->
            let* _ = require_identity t in
            let* member = dictionary_definition t name in
            Ok (Some (name, member))
        | Domain_function (t, name) ->
            let* _ = require_identity t in
            let* member = definition t name in
            Ok (Some (name, member))))
  in
  Ok (List.filter_opt members)

type value_template =
  | Int_dictionary
  | List_dictionary
  | Option_dictionary
  | Tuple_dictionary of int

let value_templates ?(dictionaries = false) types requested =
  List.filter_map (domain_nodes ~dictionaries types requested) ~f:(function
    | Domain_function _ | Value_dictionary (_, None) -> None
    | Value_dictionary (t, Some _) -> (
        if is_int types t then Some Int_dictionary
        else
          match desc types t with
          | Tconstr (path, [ _ ], _) when Path.same path Predef.path_list ->
              Some List_dictionary
          | Tconstr (path, [ _ ], _) when Path.same path Predef.path_option ->
              Some Option_dictionary
          | Ttuple components -> Some (Tuple_dictionary (List.length components))
          | _ -> None))
  |> List.dedup_and_sort ~compare:Poly.compare

(** Runtime fields preserve their source value domain; mathematical ghost fields retain
    scalar integer bounds. *)
let field_member ?(ghost = false) types ~loc name typ (t : Types.type_expr) =
  let constraint_ =
    if ghost then Option.some_if (is_int types t) Prelude.in_range
    else constraint_name types t
  in
  let where =
    Option.map constraint_ ~f:(fun name ->
        Qualified_name.raven ~loc (Qualified_name.of_string name))
  in
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
    | Tvar _ -> true
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
          (Some (if d.empty then R.Type.tuple ~loc:l [] else R.Type.data ~loc:l variants))
  in
  let domain =
    match (d.library, d.value_constraint) with
    | Some _, Some constraint_ ->
        [
          R.Member.free
            (R.Member.callable
               (R.Callable.func ~loc:l
                  ~formals:
                    [
                      R.Var.make ~loc:l
                        (R.Ident.make ~loc:l "source$value")
                        (R.Type.named ~loc:l (R.Name.make ~loc:l "T") []);
                    ]
                  ~returns:
                    [
                      R.Var.make ~loc:l
                        (R.Ident.make ~loc:l "source$admissible")
                        (R.Type.bool ~loc:l);
                    ]
                  (R.Ident.make ~loc:l constraint_.Qualified_name.name)
                  None));
        ]
    | None, _ | Some _, None -> []
  in
  Ok (R.Member.module_ ~loc:l (R.Ident.make ~loc:l d.module_name) (t :: domain))
