(** Functions over a GADT witness whose calls wait to be helped, as helping keeps one
    function's atomic updates: each is one procedure taking its witness as a value and
    returning a universal result, with a case per constructor of the witness carrying that
    constructor's result. *)

open Base

let ( let* ) = Result.( >>= )

type t = {
  original : Procedures.func;
  position : int;  (** The witness's position among the parameters. *)
  witness : Ident.t;
  universal : Procedures.func;
  result : Datatypes.t;  (** The universal result type. *)
}

(** Source argument positions retained by a universal procedure's worker. *)
let argument_projection ~at specializations (worker : Polymorphic_functions.t) =
  match
    List.find specializations ~f:(fun specialization ->
        Ident.same specialization.universal.id worker.id)
  with
  | None -> Ok None
  | Some specialization ->
      let* source =
        Polymorphic_functions.discover ~at specialization.original.scheme_type
      in
      let* positions =
        Result.all
          (List.map worker.scheme.variables ~f:(fun variable ->
               Report.expect ~at "A source argument for the AU carrier"
                 (List.findi source.variables ~f:(fun _ source ->
                      Polymorphic_functions.same_variable source variable)
                 |> Option.map ~f:fst)))
      in
      Ok (Some positions)

(** The witness parameter of [f], with its position, the witness and its arguments. *)
let witness_parameter types (f : Procedures.func) =
  List.find_mapi f.params ~f:(fun position (param : Typedtree.function_param) ->
      match param.fp_kind with
      | Tparam_pat { pat_desc = Tpat_var (id, _, _); pat_type; _ } ->
          Option.map (Witnesses.witness_type types pat_type)
            ~f:(fun (data, witness, arguments) ->
              (position, id, (data, witness), arguments))
      | _ -> None)

(** The universal result type of the witness [data]: its parameters are the witness's
    other than its indices, and each constructor's case carries the constructor's index
    types, as a tuple if several. *)
let result_type ~name (data : Datatypes.t) (witness : Datatypes.witness) =
  let id = Ident.create_local name in
  let parameters =
    List.filter_map witness.indices ~f:(fun index ->
        Option.some_if (not index) (Btype.newgenvar ()))
  in
  let* ctors =
    Result.all
      (List.map data.ctors ~f:(fun (c : Datatypes.ctor) ->
           let results =
             List.Assoc.find_exn witness.results c.raven ~equal:String.equal
           in
           let positions = List.zip_exn witness.indices results in
           let own =
             List.filter_map positions ~f:(fun (index, t) -> Option.some_if (not index) t)
           in
           let* payloads =
             Result.all
               (List.filter_map positions ~f:(fun (index, t) ->
                    Option.some_if index
                      (match Datatypes.instantiate_alias own parameters t with
                      | Some t -> Ok t
                      | None -> Report.internal data.at "A witness's index type")))
           in
           let payload =
             match payloads with
             | [ t ] -> t
             | ts -> Btype.newgenty (Ttuple (List.map ts ~f:(fun t -> (None, t))))
           in
           Ok
             {
               Datatypes.ocaml = c.ocaml;
               raven = c.raven;
               fields = [ c.raven ^ "_0" ];
               args = [ payload ];
             }))
  in
  Ok
    ( id,
      {
        Datatypes.list with
        id = Some id;
        paths = [ Path.Pident id ];
        module_name = name;
        ctors;
        parameters;
        at = data.at;
      } )

(** Whether [t] mentions one of the types [ids]. *)
let rec mentions ids t =
  match Types.get_desc t with
  | Tconstr (Pident id, [], _) when List.mem ids id ~equal:Ident.same -> true
  | _ ->
      let found = ref false in
      Btype.iter_type_expr (fun t -> if mentions ids t then found := true) t;
      !found

(** [f]'s type with its witness's index types, univars of its scheme, the universal
    [result] at the witness's other arguments. *)
let scheme (f : Procedures.func) (witness : Datatypes.witness) arguments ~result_id =
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
  let positions = List.zip_exn witness.indices arguments in
  let* ordinary =
    Result.all
      (List.filter_map positions ~f:(fun (index, argument) ->
           Option.some_if (not index)
             (match univar_of argument with
             | Some univar -> Ok univar
             | None -> Report.unsupported f.loc "A witness argument of no type variable")))
  in
  let* indices =
    Result.all
      (List.filter_map positions ~f:(fun (index, argument) ->
           Option.some_if index
             (match univar_of argument with
             | Some univar -> Ok univar
             | None -> Report.unsupported f.loc "A witness index of no type variable")))
  in
  let universal =
    Btype.newgenty (Tconstr (Path.Pident result_id, ordinary, ref Types.Mnil))
  in
  (* Its index types are the universal result, which its witness's are as well: there
     they type no value. *)
  match Types.get_desc f.scheme_type with
  | Tpoly (body, univars) -> (
      match Datatypes.substitution indices (List.map indices ~f:(fun _ -> universal)) with
      | None -> Report.internal f.loc "A universal function's substitution"
      | Some substitute ->
          Ok
            (Btype.newgenty
               (Tpoly
                  ( substitute body,
                    List.filter univars ~f:(fun u ->
                        not (List.mem indices u ~equal:Types.eq_type)) ))))
  | _ ->
      Report.unsupported f.loc "A function over a witness without locally abstract types"

(** [funcs] with each function over a witness that [helped] names replaced by its
    universal procedure, the universal procedures, and their result types. *)
let run types ~helped ~targets (funcs : Procedures.func list) =
  let* specialized =
    Result.all
      (List.filter_map funcs ~f:(fun (f : Procedures.func) ->
           match witness_parameter types f with
           | Some (position, witness_id, (data, witness), arguments)
             when List.mem helped (Ident.name f.id) ~equal:String.equal
                  || List.mem targets f.id ~equal:Ident.same ->
               Some
                 (let name = Fresh_names.fresh (data.module_name ^ "$Result") in
                  let* result_id, result = result_type ~name data witness in
                  let* scheme = scheme f witness arguments ~result_id in
                  (* The body's index types are the universal result, at the body's
                     other arguments of the witness; they may type only results. *)
                  let ordinary, indices =
                    List.partition_map (List.zip_exn witness.indices arguments)
                      ~f:(fun (index, argument) ->
                        if index then Second argument else First argument)
                  in
                  let universal_type =
                    Btype.newgenty
                      (Tconstr (Path.Pident result_id, ordinary, ref Types.Mnil))
                  in
                  let index_ids =
                    List.filter_map indices ~f:(fun t ->
                        match Types.get_desc t with
                        | Tconstr (Pident id, [], _) -> Some id
                        | _ -> None)
                  in
                  let* () =
                    if
                      List.exists f.params ~f:(fun (param : Typedtree.function_param) ->
                          match param.fp_kind with
                          | Tparam_pat p | Tparam_optional_default (p, _) ->
                              (not
                                 (Witnesses.witness_type types p.pat_type
                                 |> Option.is_some))
                              && mentions index_ids p.pat_type)
                    then
                      Report.unsupported f.loc
                        "A helped function over a witness whose index types type its \
                         parameters"
                    else Ok ()
                  in
                  let id = Ident.create_local (Ident.name f.id) in
                  Ok
                    {
                      original = f;
                      position;
                      witness = witness_id;
                      result;
                      universal =
                        {
                          f with
                          id;
                          paths = [ Path.Pident id ];
                          scheme_type = scheme;
                          source_scheme = None;
                          raven_name = Fresh_names.fresh f.raven_name;
                          universal =
                            Some
                              {
                                witness = witness_id;
                                result;
                                newtypes =
                                  List.map index_ids ~f:(fun id -> (id, universal_type));
                              };
                        };
                    })
           | _ -> None))
  in
  Ok
    ( List.filter funcs ~f:(fun f ->
          not
            (List.exists specialized ~f:(fun s ->
                 Ident.same s.original.id f.Procedures.id)))
      @ List.map specialized ~f:(fun s -> s.universal),
      specialized )
