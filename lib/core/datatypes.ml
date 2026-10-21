(** OCaml's variant types as Raven data types. Raven declares a data type's constructors
    and destructors in the scope of the type, so each type gets a module of its own, named
    as the type, capitalized as Raven's type names are, with the type [T]. OCaml's lists
    and options are Raven's [List] and [Option], which Raven instantiates for their
    element types.

    A record type with a mutable field is a reference instead, with a Raven field per
    OCaml field, named after the type, as [counter_count]; so is a ref cell, with a field
    per type of contents, as [ref_Int_contents]. A record type without a mutable field is
    a data type with one constructor, named as the type. *)

open Base
module R = Raven_api

let ( let* ) = Result.( >>= )
let loc (l : Location.t) = R.Loc.make l.loc_start l.loc_end

type ctor = {
  ocaml : string;
  raven : string;  (** Uncapitalized, as Raven's constructors are. *)
  fields : string list;  (** The destructors of the arguments. *)
  args : Types.type_expr list;
}

type field = { label : string; raven_field : string; typ : Types.type_expr }

type t = {
  id : Ident.t option;  (** [None] for Raven's [List] and [Option]. *)
  module_name : string;
  ctors : ctor list;
  heap : field list option;  (** The fields of a record type with a mutable field. *)
  alias : Types.type_expr option;  (** The type that an abbreviation stands for. *)
  at : Location.t;
}

let list =
  {
    id = None;
    module_name = "List";
    ctors =
      [
        { ocaml = "[]"; raven = "nil"; fields = []; args = [] };
        { ocaml = "::"; raven = "::"; fields = [ "hd"; "tl" ]; args = [] };
      ];
    heap = None;
    alias = None;
    at = Location.none;
  }

let option =
  {
    id = None;
    module_name = "Option";
    ctors =
      [
        { ocaml = "None"; raven = "none"; fields = []; args = [] };
        { ocaml = "Some"; raven = "some"; fields = [ "value" ]; args = [] };
      ];
    heap = None;
    alias = None;
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
          module_name = String.capitalize decl.typ_name.txt;
          ctors;
          heap = None;
          alias = None;
          at;
        }
  | Ttype_record lds when List.is_empty decl.typ_params ->
      let name = decl.typ_name.txt in
      let labels =
        List.map lds ~f:(fun (ld : Typedtree.label_declaration) -> ld.ld_name.txt)
      in
      let types =
        List.map lds ~f:(fun (ld : Typedtree.label_declaration) -> ld.ld_type.ctyp_type)
      in
      let is_mutable (ld : Typedtree.label_declaration) =
        match ld.ld_mutable with Mutable -> true | Immutable -> false
      in
      let heap, ctors =
        if List.exists lds ~f:is_mutable then
          ( Some
              (List.map2_exn labels types ~f:(fun label typ ->
                   { label; raven_field = name ^ "_" ^ label; typ })),
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
          module_name = String.capitalize name;
          ctors;
          heap;
          alias = None;
          at;
        }
  | Ttype_abstract when List.is_empty decl.typ_params && Option.is_some decl.typ_manifest
    ->
      Ok
        {
          id = Some decl.typ_id;
          module_name = String.capitalize decl.typ_name.txt;
          ctors = [];
          heap = None;
          alias = Option.map decl.typ_manifest ~f:(fun ct -> ct.ctyp_type);
          at;
        }
  | Ttype_variant _ | Ttype_record _ | Ttype_abstract ->
      Report.unsupported at "A type with parameters"
  | _ -> Report.unsupported at "This type definition"

let declares (d : t) (p : Path.t) =
  match (d.id, p) with Some id, Pident id' -> Ident.same id id' | _ -> false

(** The data type of the type constructor [p]: one of [types], a list or an option. *)
let find (types : t list) (p : Path.t) =
  if Path.same p Predef.path_list then Some list
  else if Path.same p Predef.path_option then Some option
  else List.find types ~f:(fun d -> declares d p)

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

(** The data type and constructor of [cstr]. *)
let find_cstr (types : t list) (cstr : Data_types.constructor_description) =
  match Types.get_desc cstr.cstr_res with
  | Tconstr (p, _, _) ->
      Option.bind (find types p) ~f:(fun d ->
          Option.map
            (List.find d.ctors ~f:(fun c -> String.equal c.ocaml cstr.cstr_name))
            ~f:(fun c -> (d, c)))
  | _ -> None

(** Whether [p] is the path of [Stdlib.ref]. *)
let is_ref (p : Path.t) =
  match p with
  | Pdot (Pident m, "ref") -> String.equal (Ident.name m) "Stdlib"
  | _ -> false

(** Whether [p] is the path of [Stdlib.Atomic.t]. *)
let is_atomic (p : Path.t) =
  match Path.name p with "Stdlib.Atomic.t" | "Stdlib__Atomic.t" -> true | _ -> false

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
  R.Name.make ~loc:l ~path:[ d.module_name ] c.raven

(** The Raven type of the OCaml type [t]; [self] is the data type being defined, if any,
    which its module calls [T]. *)
let rec typ (types : t list) ?self ~(at : Location.t) (t : Types.type_expr) :
    (R.Type.t, Report.error) Result.t =
  let l = loc at in
  match desc types t with
  | Tconstr (p, [], _) when Path.same p Predef.path_int -> Ok (R.Type.int ~loc:l)
  | Tconstr (p, [], _) when Path.same p Predef.path_bool -> Ok (R.Type.bool ~loc:l)
  | Tconstr (p, [], _) when Path.same p Predef.path_unit -> Ok (R.Type.tuple ~loc:l [])
  | Tconstr (p, [ elt ], _)
    when Path.same p Predef.path_list || Path.same p Predef.path_option ->
      let* elt = typ types ?self ~at elt in
      let d = Option.value_exn (find types p) in
      Ok (R.Type.named ~loc:l (R.Name.make ~loc:l d.module_name) [ elt ])
  | Tconstr (p, [ _ ], _) when is_ref p || is_atomic p -> Ok (R.Type.ref ~loc:l)
  | Tconstr (p, [], _)
    when Option.exists (find types p) ~f:(fun d -> Option.is_some d.heap) ->
      Ok (R.Type.ref ~loc:l)
  | Tconstr (p, [], _) when Option.exists self ~f:(fun d -> declares d p) ->
      Ok (R.Type.named ~loc:l (R.Name.make ~loc:l "T") [])
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

(** A name for the type [t], unique among those of [types], for the names of the fields of
    ref cells, as [IntList] for [int list]. *)
let rec tag (types : t list) (t : Types.type_expr) : string =
  match desc types t with
  | Tconstr (p, [], _) when Path.same p Predef.path_int -> "Int"
  | Tconstr (p, [], _) when Path.same p Predef.path_bool -> "Bool"
  | Tconstr (p, [], _) when Path.same p Predef.path_unit -> "Unit"
  | Tconstr (p, [ elt ], _) when Path.same p Predef.path_list -> tag types elt ^ "List"
  | Tconstr (p, [ elt ], _) when Path.same p Predef.path_option ->
      tag types elt ^ "Option"
  | Tconstr (p, [ elt ], _) when is_ref p -> tag types elt ^ "Ref"
  | Tconstr (p, [ elt ], _) when is_atomic p -> tag types elt ^ "Atomic"
  | Tconstr (p, [], _) when Option.is_some (find types p) ->
      (Option.value_exn (find types p)).module_name
  | Ttuple components ->
      String.concat (List.map components ~f:(fun (_, t) -> tag types t)) ^ "Tuple"
  | Tpoly (t, []) -> tag types t
  | _ -> "Other"

let is_int types t =
  match desc types t with
  | Tconstr (p, [], _) -> Path.same p Predef.path_int
  | Tpoly (t, []) -> (
      match desc types t with
      | Tconstr (p, [], _) -> Path.same p Predef.path_int
      | _ -> false)
  | _ -> false

(** The field [name] of type [typ], for values of the OCaml type [t]: an [int] field's
    values are in [int]'s range, which owning the field then implies. *)
let field_member types ~loc name typ (t : Types.type_expr) =
  let where = Option.some_if (is_int types t) (R.Name.make ~loc Prelude.in_range) in
  R.Member.field ~loc ?where (R.Ident.make ~loc name) typ

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
  | Tconstr (p, [], _) ->
      begin match find types p with
      | Some { heap = Some _; _ } -> true
      | Some { id = Some _; ctors; _ } ->
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
    | Tconstr (p, args, _) -> begin
        List.exists args ~f:(go seen)
        ||
        match find types p with
        | Some { heap = Some _; _ } -> true
        | Some ({ id = Some id; _ } as d) when not (List.mem seen id ~equal:Ident.same) ->
            List.exists d.ctors ~f:(fun c -> List.exists c.args ~f:(go (id :: seen)))
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
let fields (types : t list) : (R.Member.t list, Report.error) Result.t =
  let field (d : t) (f : field) =
    let* typ = typ types ~at:d.at f.typ in
    let l = loc d.at in
    Ok (field_member types ~loc:l f.raven_field typ f.typ)
  in
  Result.all
    (List.concat_map types ~f:(fun d ->
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
  Ok
    (R.Member.module_ ~loc:l
       (R.Ident.make ~loc:l d.module_name)
       [
         R.Member.type_ ~loc:l (R.Ident.make ~loc:l "T")
           (Some (R.Type.data ~loc:l variants));
       ])
