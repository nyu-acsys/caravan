(** Copies of functions over a GADT witness, one per constructor they are called with:
    those whose calls wait to be helped, as helping keeps one function's atomic updates.
*)

open Base

let ( let* ) = Result.( >>= )

type copy = {
  constructor : string;  (** The constructor, by its OCaml name. *)
  copy_id : Ident.t;
  scheme : Types.type_expr;  (** The function's type with the constructor's types. *)
  newtypes : (Ident.t * Types.type_expr) list;
      (** The locally abstract types it selects, with its types for them. *)
}

type t = {
  original : Procedures.func;
  position : int;  (** The witness's position among the parameters. *)
  witness : Ident.t;
  copies : copy list;
}

(** The witness parameter of [f], with its position, the witness and its arguments. *)
let witness_parameter types (f : Procedures.func) =
  List.find_mapi f.params ~f:(fun position (param : Typedtree.function_param) ->
      match param.fp_kind with
      | Tparam_pat { pat_desc = Tpat_var (id, _, _); pat_type; _ } ->
          Option.map (Witnesses.witness_type types pat_type)
            ~f:(fun (_, witness, arguments) -> (position, id, witness, arguments))
      | _ -> None)

(** The constructors with which [funcs] call [f] at [position]. *)
let called_with funcs (f : Procedures.func) position =
  let found = ref [] in
  let expr iterator (e : Typedtree.expression) =
    (match e.exp_desc with
    | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, args)
      when List.mem f.paths path ~equal:Path.same || Path.same path (Path.Pident f.id)
      -> (
        match List.nth args position with
        | Some (_, Arg { exp_desc = Texp_construct (_, cstr, []); _ }) ->
            found := cstr.cstr_name :: !found
        | _ -> ())
    | _ -> ());
    Tast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Tast_iterator.default_iterator with expr } in
  List.iter funcs ~f:(fun (g : Procedures.func) -> iterator.expr iterator g.body);
  List.dedup_and_sort !found ~compare:String.compare

(** [f]'s type with the constructor [ctor]'s index types for the witness's indices. *)
let scheme (f : Procedures.func) (witness : Datatypes.witness) arguments ctor =
  let univar_of argument =
    match Types.get_desc argument with
    | Tconstr (Pident id, [], _) ->
        let rec find t =
          match Types.get_desc t with
          | Tpoly (_, univars) ->
              List.find univars ~f:(fun u ->
                  match Types.get_desc u with
                  | Tunivar (Some name) -> String.equal name (Ident.name id)
                  | _ -> false)
          | _ -> None
        in
        find f.scheme_type
    | _ -> None
  in
  let results =
    List.Assoc.find_exn witness.results (String.uncapitalize ctor) ~equal:String.equal
  in
  let positions = List.zip_exn witness.indices (List.zip_exn results arguments) in
  (* The constructor's own variables are the function's for the ordinary arguments. *)
  let* ordinary =
    Result.all
      (List.filter_map positions ~f:(fun (index, (own, argument)) ->
           Option.some_if (not index)
             (match univar_of argument with
             | Some univar -> Ok (own, univar)
             | None -> Report.unsupported f.loc "A witness argument of no type variable")))
  in
  let* indices =
    Result.all
      (List.filter_map positions ~f:(fun (index, (index_type, argument)) ->
           Option.some_if index
             (match
                ( univar_of argument,
                  Datatypes.instantiate_alias (List.map ordinary ~f:fst)
                    (List.map ordinary ~f:snd) index_type )
              with
             | Some univar, Some typ -> Ok (univar, typ)
             | _ -> Report.unsupported f.loc "A witness index of no type variable")))
  in
  match Types.get_desc f.scheme_type with
  | Tpoly (body, univars) -> (
      match
        Datatypes.substitution (List.map indices ~f:fst) (List.map indices ~f:snd)
      with
      | None -> Report.internal f.loc "A specialization's substitution"
      | Some substitute ->
          Ok
            (Btype.newgenty
               (Tpoly
                  ( substitute body,
                    List.filter univars ~f:(fun u ->
                        not (List.mem (List.map indices ~f:fst) u ~equal:Types.eq_type))
                  ))))
  | _ ->
      Report.unsupported f.loc "A function over a witness without locally abstract types"

(** [funcs] with each function over a witness that [helped] names replaced by its copies,
    and those copies. *)
let run types ~helped (funcs : Procedures.func list) =
  let* specialized =
    Result.all
      (List.filter_map funcs ~f:(fun (f : Procedures.func) ->
           match witness_parameter types f with
           | Some (position, witness_id, witness, arguments)
             when List.mem helped (Ident.name f.id) ~equal:String.equal ->
               Some
                 (let* copies =
                    Result.all
                      (List.map (called_with funcs f position) ~f:(fun constructor ->
                           let* scheme = scheme f witness arguments constructor in
                           let aliases, _ =
                             Witnesses.refinement witness arguments
                               (String.uncapitalize constructor)
                           in
                           Ok
                             {
                               constructor;
                               newtypes =
                                 List.filter_map aliases ~f:(fun data ->
                                     Option.both data.Datatypes.id data.alias);
                               copy_id =
                                 Ident.create_local (Ident.name f.id ^ "$" ^ constructor);
                               scheme;
                             }))
                  in
                  Ok { original = f; position; witness = witness_id; copies })
           | _ -> None))
  in
  let copies =
    List.concat_map specialized ~f:(fun s ->
        List.map s.copies ~f:(fun copy ->
            {
              s.original with
              id = copy.copy_id;
              paths = [ Path.Pident copy.copy_id ];
              scheme_type = copy.scheme;
              raven_name =
                Fresh_names.fresh
                  (s.original.raven_name ^ "$" ^ String.uncapitalize copy.constructor);
              copy_for =
                Some
                  {
                    constructor = copy.constructor;
                    witness = s.witness;
                    newtypes = copy.newtypes;
                  };
            }))
  in
  Ok
    ( List.filter funcs ~f:(fun f ->
          not
            (List.exists specialized ~f:(fun s ->
                 Ident.same s.original.id f.Procedures.id)))
      @ copies,
      specialized )
