(** Optional defaults enter the ordinary body after the option-valued inputs. *)

open Base
open Typedtree

let ( let* ) = Result.( >>= )

let option_constructors ~at environment =
  let* declaration =
    match Env.find_type Predef.path_option environment with
    | declaration -> Ok declaration
    | exception Stdlib.Not_found ->
        Error (Report.error Type at "The compiler's option type is unavailable")
  in
  let constructors =
    Datarepr.constructors_of_type ~current_unit:None Predef.path_option declaration
  in
  let find name =
    Report.expect ~at
      ("The compiler's option constructor " ^ name)
      (List.find_map constructors ~f:(fun (_, constructor) ->
           Option.some_if (String.equal constructor.Data_types.cstr_name name) constructor))
  in
  let* none = find "None" in
  let* some = find "Some" in
  Ok (none, some)

let uid = Shape.Uid.internal_not_actually_unique

let expression template ~at typ desc =
  {
    template with
    exp_desc = desc;
    exp_type = typ;
    exp_loc = at;
    exp_extra = [];
    exp_attributes = [];
  }

let reference template ~at id typ =
  expression template ~at typ
    (Texp_ident
       ( Path.Pident id,
         Location.mkloc (Longident.Lident (Ident.name id)) at,
         {
           Types.val_type = typ;
           val_kind = Val_reg;
           val_loc = at;
           val_attributes = [];
           val_uid = uid;
         } ))

let variable pattern ~at id typ =
  {
    pattern with
    pat_desc = Tpat_var (id, Location.mkloc (Ident.name id) at, uid);
    pat_loc = at;
    pat_type = typ;
    pat_extra = [];
    pat_attributes = [];
  }

let input parameter pattern typ =
  let id =
    if List.mem (Typedtree.pat_bound_idents pattern) parameter.fp_param ~equal:Ident.same
    then Ident.create_local (Ident.name parameter.fp_param)
    else parameter.fp_param
  in
  let pattern = variable pattern ~at:parameter.fp_loc id typ in
  ({ parameter with fp_param = id; fp_kind = Tparam_pat pattern }, pattern)

let bind parameter pattern selected body =
  let at = parameter.fp_loc in
  let extent = { at with Location.loc_end = body.exp_loc.loc_end } in
  match pattern.pat_desc with
  | Tpat_var _ ->
      let binding =
        {
          vb_pat = pattern;
          vb_expr = selected;
          vb_rec_kind = Value_rec_types.Dynamic;
          vb_attributes = [];
          vb_loc = at;
        }
      in
      expression body ~at:extent body.exp_type
        (Texp_let (Nonrecursive, [ binding ], body))
  | _ ->
      let case =
        {
          c_lhs = Typedtree.as_computation_pattern pattern;
          c_cont = None;
          c_guard = None;
          c_rhs = body;
        }
      in
      expression body ~at:extent body.exp_type
        (Texp_match (selected, [ case ], [], parameter.fp_partial))

let lower params body =
  if
    not
      (List.exists params ~f:(fun parameter ->
           match parameter.fp_kind with
           | Tparam_optional_default _ -> true
           | Tparam_pat _ -> false))
  then Ok (params, body)
  else
    List.fold_right params
      ~init:(Ok ([], body))
      ~f:(fun (parameter : function_param) rest ->
        let* params, body = rest in
        match parameter.fp_kind with
        | Tparam_pat { pat_desc = Tpat_var _; _ } -> Ok (parameter :: params, body)
        | Tparam_pat pattern ->
            let native, _ = input parameter pattern pattern.pat_type in
            let selected =
              reference body ~at:parameter.fp_loc native.fp_param pattern.pat_type
            in
            Ok (native :: params, bind parameter pattern selected body)
        | Tparam_optional_default (pattern, default) ->
            let at = parameter.fp_loc in
            let* none, some = option_constructors ~at default.exp_env in
            let option_type = Predef.type_option pattern.pat_type in
            let native, input_pattern = input parameter pattern option_type in
            let supplied = Ident.create_local "optional_value" in
            let supplied_pattern = variable pattern ~at supplied pattern.pat_type in
            let arm constructor arguments rhs =
              let constructor =
                {
                  constructor with
                  Data_types.cstr_res = option_type;
                  cstr_args = List.map arguments ~f:(fun argument -> argument.pat_type);
                }
              in
              let pattern =
                {
                  input_pattern with
                  pat_desc =
                    Tpat_construct
                      ( Location.mkloc (Longident.Lident constructor.cstr_name) at,
                        constructor,
                        arguments,
                        None );
                }
              in
              {
                c_lhs = Typedtree.as_computation_pattern pattern;
                c_cont = None;
                c_guard = None;
                c_rhs = rhs;
              }
            in
            let selected =
              expression default ~at pattern.pat_type
                (Texp_match
                   ( reference default ~at native.fp_param option_type,
                     [
                       arm some [ supplied_pattern ]
                         (reference default ~at supplied pattern.pat_type);
                       arm none [] default;
                     ],
                     [],
                     Total ))
            in
            Ok (native :: params, bind parameter pattern selected body))
