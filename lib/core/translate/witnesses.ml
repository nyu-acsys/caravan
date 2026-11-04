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
      (* The conversions of [owner], with [body] for the constructor and index. *)
      let conversions ~owner ~ensures ~body =
        all_results witness.results ~f:(fun (ctor, arguments) ->
            let types = bind types ~owner ~at:data.at witness arguments in
            all_results (index_types witness arguments) ~f:(fun (position, index_type) ->
                let* formal = Datatypes.typ types ~at:data.at index_type in
                let ensures =
                  if ensures then
                    let admissible =
                      Option.to_list (Datatypes.admissible ~loc:l types index_type x)
                    in
                    [
                      R.Spec.make
                        (R.Expr.binary ~loc:l Impl
                           (List.reduce_exn ~f:(R.Expr.binary ~loc:l And)
                              (R.Expr.binary ~loc:l Eq
                                 (R.Expr.var ~loc:l (name "tag"))
                                 (tag ctor)
                              :: admissible))
                           (call
                              (parameter position ^ ".holds")
                              [ R.Expr.var ~loc:l (name "y") ]));
                    ]
                  else []
                in
                Ok
                  (R.Member.callable
                     (R.Callable.func ~loc:l
                        ~formals:[ R.Var.make ~loc:l (ident "x") formal ]
                        ~returns:[ R.Var.make ~loc:l (ident "y") (carrier position) ]
                        ~ensures
                        (ident (conversion ctor position))
                        (body ctor position)))))
        |> Result.map ~f:List.concat
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
      let* interface_conversions =
        conversions ~owner:[ interface ] ~ensures:true ~body:(fun _ _ -> None)
      in
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
            let arbitrary position = "any$" ^ parameter position in
            let* own_conversions =
              conversions ~owner ~ensures:false ~body:(fun other position ->
                  Some
                    (if String.equal other ctor then x
                     else R.Expr.var ~loc:l (name (arbitrary position))))
            in
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
