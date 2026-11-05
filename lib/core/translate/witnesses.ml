(** GADT witnesses: for a witness type, the interface of its witnesses, with the value
    dictionaries of its parameters, the tag of its constructor and per constructor and
    index the conversion from the constructor's index type, and a functor per constructor
    implementing it. *)

open Base
module R = Raven_api

let ( let* ) = Result.( >>= )
let all_results list ~f = Result.all (List.map list ~f)
let interface_name (data : Datatypes.t) = data.module_name ^ "$Witness"

let functor_name (data : Datatypes.t) (ctor : Datatypes.ctor) =
  data.module_name ^ "$" ^ ctor.ocaml

let parameter index = "A" ^ Int.to_string index
let conversion ctor index = ctor ^ "$to$" ^ parameter index
let conversion_from ctor index = ctor ^ "$from$" ^ parameter index
let arbitrary index = "any$" ^ parameter index
let arbitrary_index ctor index = "any$" ^ ctor ^ "$" ^ parameter index

(** The data types with the ordinary ones of [arguments], a constructor's result
    arguments, as the dictionaries [A<i>] of [owner]. *)
let bind types ~owner ~at (witness : Datatypes.witness) arguments =
  List.filter_mapi (List.zip_exn witness.indices arguments)
    ~f:(fun position (index, argument) ->
      Option.some_if (not index)
        (Datatypes.variable_type ~variable:argument ~owner ~parameter:(parameter position)
           ~at))
  @ types

(** The index types of the constructor with [arguments], by position. *)
let index_types (witness : Datatypes.witness) arguments =
  List.filter_mapi (List.zip_exn witness.indices arguments)
    ~f:(fun position (index, argument) -> Option.some_if index (position, argument))

(** The value dictionaries that [requested] need in [owner]: those to declare there, and
    those outside it. *)
let dictionaries types ~owner requested =
  let* declarations = Datatypes.domain_members ~dictionaries:true types requested in
  Ok
    (List.partition_tf declarations ~f:(fun (qualified, _) ->
         List.equal String.equal (Qualified_name.of_string qualified).path owner))

let members types (data : Datatypes.t) =
  match data.witness with
  | None -> Ok ([], [])
  | Some witness ->
      let l = Datatypes.loc data.at in
      let ident text = R.Ident.make ~loc:l text in
      let name text = Qualified_name.raven ~loc:l (Qualified_name.of_string text) in
      let call text arguments = R.Expr.call ~loc:l (name text) arguments in
      let value_interface = name Prelude.value_interface in
      let carrier position =
        R.Type.named ~loc:l (name (parameter position ^ ".Carrier")) []
      in
      let tag_type =
        R.Type.named ~loc:l
          (name
             (String.concat ~sep:"."
                (Option.value data.module_path ~default:[ data.module_name ])
             ^ ".T"))
          []
      in
      let tag ctor =
        R.Expr.call ~loc:l
          (Datatypes.ctor_name ~loc:l data
             (List.find_exn data.ctors ~f:(fun c -> String.equal c.raven ctor)))
          []
      in
      let x = R.Expr.var ~loc:l (name "x") in
      (* The conversions of [owner], to and from each constructor's index types: the
         interface's, specified, if [own] is [None], or those of the implementation of
         the constructor [own], the identity for it and arbitrary for the others. *)
      let conversions ~owner ~own =
        all_results witness.results ~f:(fun (ctor, arguments) ->
            let types = bind types ~owner ~at:data.at witness arguments in
            all_results (index_types witness arguments) ~f:(fun (position, index_type) ->
                let* index = Datatypes.typ types ~at:data.at index_type in
                let to_ = conversion ctor position
                and from = conversion_from ctor position in
                let variable text = R.Expr.var ~loc:l (name text) in
                let when_tag conditions conclusion =
                  R.Spec.make
                    (R.Expr.binary ~loc:l Impl
                       (List.reduce_exn ~f:(R.Expr.binary ~loc:l And)
                          (R.Expr.binary ~loc:l Eq (variable "tag") (tag ctor)
                          :: conditions))
                       conclusion)
                in
                let admissible =
                  Option.to_list (Datatypes.admissible ~loc:l types index_type x)
                in
                let holds = call (parameter position ^ ".holds") [ variable "y" ] in
                let to_ensures, from_ensures =
                  match own with
                  | Some _ -> ([], [])
                  | None ->
                      ( [
                          when_tag admissible holds;
                          when_tag []
                            (R.Expr.binary ~loc:l Eq (call from [ variable "y" ]) x);
                        ],
                        [
                          when_tag [ holds ]
                            (Option.value (List.hd admissible)
                               ~default:(R.Expr.bool ~loc:l true));
                          when_tag []
                            (R.Expr.binary ~loc:l Eq (call to_ [ x ]) (variable "y"));
                        ] )
                in
                let body own_value other =
                  Option.map own ~f:(fun own ->
                      if String.equal own ctor then own_value else variable other)
                in
                let members =
                  [
                    R.Member.callable
                      (R.Callable.func ~loc:l
                         ~formals:[ R.Var.make ~loc:l (ident "x") index ]
                         ~returns:[ R.Var.make ~loc:l (ident "y") (carrier position) ]
                         ~ensures:to_ensures (ident to_)
                         (body x (arbitrary position)));
                    R.Member.callable
                      (R.Callable.func ~loc:l
                         ~formals:[ R.Var.make ~loc:l (ident "y") (carrier position) ]
                         ~returns:[ R.Var.make ~loc:l (ident "x") index ]
                         ~ensures:from_ensures (ident from)
                         (body (variable "y") (arbitrary_index ctor position)));
                  ]
                in
                (* An implementation's arbitrary values of the other constructors' index
                   types. *)
                match own with
                | Some own when not (String.equal own ctor) ->
                    Ok
                      (R.Member.free
                         (R.Member.value ~loc:l ~typ:index
                            (ident (arbitrary_index ctor position))
                            None)
                      :: members)
                | _ -> Ok members))
        |> Result.map ~f:(fun members -> List.concat (List.concat members))
      in
      let requested owner =
        List.concat_map witness.results ~f:(fun (_, arguments) ->
            let types = bind types ~owner ~at:data.at witness arguments in
            List.map (index_types witness arguments) ~f:(fun (_, t) -> (types, t)))
      in
      let declarations owner =
        let* parts =
          all_results (requested owner) ~f:(fun (types, t) ->
              dictionaries types ~owner [ t ])
        in
        Ok
          ( Datatypes.unique_domain_members (List.concat_map parts ~f:fst),
            Datatypes.unique_domain_members (List.concat_map parts ~f:snd) )
      in
      let templates owner =
        List.concat_map (requested owner) ~f:(fun (types, t) ->
            Datatypes.value_templates ~dictionaries:true types [ t ])
      in
      let interface = interface_name data in
      let* local, external_ = declarations [ interface ] in
      let* interface_conversions = conversions ~owner:[ interface ] ~own:None in
      let interface_member =
        R.Member.module_ ~loc:l ~interface:true (ident interface)
          (List.mapi witness.indices ~f:(fun position _ ->
               R.Member.instance ~loc:l (ident (parameter position)) value_interface)
          @ [ R.Member.value ~loc:l ~typ:tag_type (ident "tag") None ]
          @ List.map local ~f:snd @ interface_conversions)
      in
      let* functors =
        all_results witness.results ~f:(fun (ctor, arguments) ->
            let owner_ctor =
              List.find_exn data.ctors ~f:(fun c -> String.equal c.raven ctor)
            in
            let module_name = functor_name data owner_ctor in
            let owner = [ module_name ] in
            let types = bind types ~owner ~at:data.at witness arguments in
            let ordinary =
              List.filter_mapi witness.indices ~f:(fun position index ->
                  Option.some_if (not index) position)
            in
            let* indices =
              all_results (index_types witness arguments) ~f:(fun (position, t) ->
                  match Datatypes.dictionary_name types t with
                  | Some dictionary ->
                      Ok
                        (R.Member.alias ~loc:l ~typ:value_interface
                           (ident (parameter position))
                           (name dictionary))
                  | None -> Report.unsupported data.at "This witness index's dictionary")
            in
            let* own_conversions = conversions ~owner ~own:(Some ctor) in
            Ok
              (R.Member.module_ ~loc:l
                 ~params:
                   (List.map ordinary ~f:(fun position ->
                        (ident ("P" ^ Int.to_string position), value_interface)))
                 ~implements:[ (name interface, []) ]
                 (ident module_name)
                 (List.map ordinary ~f:(fun position ->
                      R.Member.alias ~loc:l ~typ:value_interface
                        (ident (parameter position))
                        (name ("P" ^ Int.to_string position)))
                 @ indices
                 @ [ R.Member.value ~loc:l ~typ:tag_type (ident "tag") (Some (tag ctor)) ]
                 @ List.filter_map (index_types witness arguments)
                     ~f:(fun (position, _) ->
                       Option.some_if
                         (List.length witness.results > 1)
                         (R.Member.free
                            (R.Member.value ~loc:l ~typ:(carrier position)
                               (ident (arbitrary position))
                               None)))
                 @ own_conversions)))
      in
      Ok
        ( external_
          @ (interface, interface_member)
            :: List.map2_exn witness.results functors ~f:(fun (ctor, _) member ->
                ( functor_name data
                    (List.find_exn data.ctors ~f:(fun c -> String.equal c.raven ctor)),
                  member )),
          templates [ interface ] )

(** The witness data type and arguments of [typ], if it is a witness. *)
let witness_type types typ =
  match Datatypes.desc types typ with
  | Tconstr (path, arguments, _) ->
      Option.bind (Datatypes.find types path) ~f:(fun data ->
          Option.map data.Datatypes.witness ~f:(fun witness -> (data, witness, arguments)))
  | _ -> None

(** Whether [argument], a type in a function's body, is its scheme's [variable]: the
    variable itself, or the locally abstract type of its name. *)
let denotes variable argument =
  Polymorphic_functions.same_variable variable argument
  ||
  match (Types.get_desc variable, Types.get_desc argument) with
  | Tunivar (Some name), Tconstr (Pident id, [], _) -> String.equal (Ident.name id) name
  | _ -> false

(** The witness parameter of a function with [params], whose scheme has [variables]: one
    of a witness type whose arguments are distinct variables of the scheme. *)
let parameter types ~at ~variables (params : Typedtree.function_param list) =
  let candidates =
    List.filter_mapi params ~f:(fun position (param : Typedtree.function_param) ->
        match param.fp_kind with
        | Tparam_pat pattern ->
            Option.map (witness_type types pattern.pat_type) ~f:(fun found ->
                (position, found))
        | Tparam_optional_default _ -> None)
  in
  match candidates with
  | [] -> Ok None
  | _ :: _ :: _ -> Report.unsupported at "A function with several witness parameters"
  | [ (position, (data, _, arguments)) ] ->
      let members =
        List.map variables ~f:(fun variable ->
            List.findi arguments ~f:(fun _ argument -> denotes variable argument)
            |> Option.map ~f:fst)
      in
      let covered = List.filter_opt members in
      if
        List.length covered = List.length arguments
        && List.length (List.dedup_and_sort covered ~compare:Int.compare)
           = List.length covered
      then
        Ok
          (Some
             Polymorphic_functions.
               { parameter = position; interface = interface_name data; members })
      else
        Report.unsupported at
          "A witness parameter whose types are not the function's distinct type variables"

(** The witness of the worker [current], if a witness with the type [arguments] is its
    own: its type parameters are the worker's variables that the witness's are. *)
let own_witness (current : Polymorphic_functions.t option) arguments =
  Option.bind current ~f:(fun worker ->
      Option.bind worker.witness ~f:(fun witness ->
          let mine =
            List.for_alli arguments ~f:(fun position argument ->
                List.existsi witness.members ~f:(fun index member ->
                    Option.equal Int.equal member (Some position)
                    && denotes (List.nth_exn worker.scheme.variables index) argument))
          in
          Option.some_if mine (worker.name ^ ".W")))

(** In a case for the constructor [ctor] of a match on a witness with the type
    [arguments]: the locally abstract types among its indices as abbreviations of the
    constructor's index types, and those types with their positions. *)
let refinement (witness : Datatypes.witness) arguments ctor =
  let results = List.Assoc.find_exn witness.results ctor ~equal:String.equal in
  let positions = List.zip_exn witness.indices (List.zip_exn results arguments) in
  let parameters, actuals =
    List.unzip
      (List.filter_map positions ~f:(fun (index, pair) -> Option.some_if (not index) pair))
  in
  List.filter_mapi positions ~f:(fun position (index, (index_type, argument)) ->
      match Types.get_desc argument with
      | Tconstr (Pident id, [], _) when index ->
          Option.map (Datatypes.instantiate_alias parameters actuals index_type)
            ~f:(fun body -> (Datatypes.local_alias id body, (id, position)))
      | _ -> None)
  |> List.unzip

(** For a contract's case for the constructor [ctor] of a match on a value of the witness
    type [scrutinee], in the worker [current]: the abbreviations there, and the variables
    of [var_types] whose types it refines, each with the conversion that reads it at the
    constructor's index type. *)
type read =
  | Conversion of string  (** A worker's conversion function from the index type. *)
  | Payload of string  (** The field of a universal result's case. *)

let contract_case ?universal types ~(current : Polymorphic_functions.t option) ~scrutinee
    ~var_types ctor =
  match witness_type types scrutinee with
  | None -> None
  | Some (_, witness, arguments) ->
      let own = own_witness current arguments in
      let ctor = String.uncapitalize ctor in
      if not (List.Assoc.mem witness.results ctor ~equal:String.equal) then None
      else
        let aliases, refined = refinement witness arguments ctor in
        (* In a universal procedure, a variable of an index type is a universal result,
           whose case's payload the constructor's case reads. *)
        let read position =
          match (universal, own) with
          | Some (result : Datatypes.t), _ ->
              Option.map
                (List.find result.ctors ~f:(fun c -> String.equal c.raven ctor))
                ~f:(fun c -> Payload (List.hd_exn c.fields))
          | None, Some own ->
              Some (Conversion (own ^ "." ^ conversion_from ctor position))
          | None, None -> None
        in
        let reads =
          List.filter_map var_types ~f:(fun (x, typ) ->
              match Types.get_desc typ with
              | Tconstr (Pident id, [], _) ->
                  Option.bind (List.Assoc.find refined id ~equal:Ident.same)
                    ~f:(fun position -> Option.map (read position) ~f:(fun r -> (x, r)))
              | _ -> None)
        in
        Some (aliases, reads)

(** For a match of type [result] on a value of the witness type [scrutinee], in the worker
    [current]: per case, by its right-hand side, the data types in which the locally
    abstract types its constructor refines are its index types, and the conversion of its
    value to [result] if that is an index; [None] if [scrutinee] is no witness. *)
let arms ?universal types ~at ~(current : Polymorphic_functions.t option) ~scrutinee
    ~result (cases : (Typedtree.pattern * Typedtree.expression) list) =
  match witness_type types scrutinee with
  | None -> Ok None
  | Some (_, witness, arguments) ->
      let same left right =
        match (Types.get_desc left, Types.get_desc right) with
        | Tconstr (Pident a, [], _), Tconstr (Pident b, [], _) -> Ident.same a b
        | _ -> Types.eq_type left right
      in
      let result_index =
        List.findi (List.zip_exn witness.indices arguments) ~f:(fun _ (index, argument) ->
            index && same argument result)
        |> Option.map ~f:fst
      in
      let own = own_witness current arguments in
      let* () =
        match (result_index, own, universal) with
        | Some _, None, None ->
            Report.unsupported at "A match on a witness other than the function's own"
        | _ -> Ok ()
      in
      (* In a universal procedure, a case's value is its constructor's case of the
         universal result. *)
      let convert ctor position =
        match (universal, own) with
        | Some (result : Datatypes.t), _ ->
            Option.map
              (List.find result.ctors ~f:(fun c -> String.equal c.raven ctor))
              ~f:(fun c -> result.module_name ^ "." ^ c.raven)
        | None, Some own -> Some (own ^ "." ^ conversion ctor position)
        | None, None -> None
      in
      let constructor (p : Typedtree.pattern) =
        match p.pat_desc with
        | Tpat_construct (_, cstr, [], _) -> Some (String.uncapitalize cstr.cstr_name)
        | _ -> None
      in
      Ok
        (Some
           (fun (rhs : Typedtree.expression) ->
             let ctor =
               List.find_map cases ~f:(fun (p, candidate) ->
                   Option.some_if (phys_equal candidate rhs) p)
               |> Option.bind ~f:constructor
             in
             match ctor with
             | None -> (types, None)
             | Some ctor ->
                 let aliases, _ = refinement witness arguments ctor in
                 ( aliases @ types,
                   Option.bind result_index ~f:(fun position -> convert ctor position) )))
