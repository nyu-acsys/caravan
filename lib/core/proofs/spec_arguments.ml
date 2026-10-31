(** Free names supplied directly as predicate arguments. *)

open Base
module S = Caravan_spec.Spec_ast

let predicate_parameters ~lookup ~bound terms =
  let rec spine (term : S.term) arguments =
    match term.term_desc with
    | Tapply (callee, argument) -> spine callee (argument :: arguments)
    | _ -> (term, arguments)
  in
  let rec collect bound (term : S.term) =
    let head, arguments = spine (S.chain term) [] in
    let here =
      match head.term_desc with
      | Tvar (Qid id) when List.mem bound id.pid_str ~equal:String.equal -> []
      | Tvar name ->
          begin match lookup name with
          | Some types when List.length arguments <= List.length types ->
              List.filter_map
                (List.zip_exn arguments (List.take types (List.length arguments)))
                ~f:(fun (argument, typ) ->
                  match argument.S.term_desc with
                  | Tvar (Qid id) when not (List.mem bound id.pid_str ~equal:String.equal)
                    ->
                      Some (id, typ)
                  | _ -> None)
          | _ -> []
          end
      | _ -> []
    in
    let nested =
      match term.term_desc with
      | Tapply (left, right) | Tinfix (left, _, right) ->
          collect bound left @ collect bound right
      | Tfield (term, _) | Tattr (_, term) | Tcast (term, _) | Told term ->
          collect bound term
      | Tif (condition, yes, no) ->
          List.concat_map [ condition; yes; no ] ~f:(collect bound)
      | Tquant (_, binders, body) ->
          collect (List.map binders ~f:(fun (id, _) -> id.S.pid_str) @ bound) body
      | Tcomprehension ((id, _), body) -> collect (id.pid_str :: bound) body
      | Tlet (pattern, rhs, body) ->
          collect bound rhs @ collect (Source.logical_pattern_names pattern @ bound) body
      | Tmatch (value, cases) ->
          collect bound value
          @ List.concat_map cases ~f:(fun (pattern, body) ->
              collect (Source.logical_pattern_names pattern @ bound) body)
      | Ttuple values -> List.concat_map values ~f:(collect bound)
      | Trecord (base, fields) ->
          List.concat_map (S.record_terms base fields) ~f:(collect bound)
      | Ttrue | Tfalse | Tconst _ | Tvar _ -> []
    in
    here @ nested
  in
  List.concat_map terms ~f:(collect bound)
