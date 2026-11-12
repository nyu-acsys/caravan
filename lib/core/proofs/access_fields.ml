(** Typed declarations of ordinary fields with an explicit shared-access discipline. *)

open Base
module S = Caravan_spec.Spec_ast

let ( let* ) = Result.( >>= )

type t = {
  name : S.id;
  kind : S.access_kind;
  owner_type : Types.type_expr;
  receiver_pattern : Typedtree.pattern;
  value_type : Types.type_expr;
  label : Data_types.label_description;
  record_path : Path.t;
  at : Location.t;
}

let error ?related at message = Error (Report.error ?related Type at message)

let compiler ~at f =
  try Ok (f ())
  with exn ->
    let exn = Compiler_types.diagnostic_exception exn in
    Error
      (Option.value (Report.of_exn exn)
         ~default:(Report.error Type at (Stdlib.Printexc.to_string exn)))

let same_field left right =
  Path.same left.record_path right.record_path
  && Int.equal left.label.lbl_pos right.label.lbl_pos

let kind_name = function S.Frozen -> "Ghost.Frozen" | Relaxed -> "Ghost.Relaxed"

let validate_registry fields =
  let rec check seen = function
    | [] -> Ok ()
    | field :: rest ->
        begin match List.find seen ~f:(same_field field) with
        | None -> check (field :: seen) rest
        | Some previous ->
            let related = [ (previous.at, "Its first field facade") ] in
            if Poly.equal previous.kind field.kind then check seen rest
            else
              error ~related field.at
                (Printf.sprintf
                   "The field %s cannot use both Ghost.Frozen and Ghost.Relaxed"
                   field.label.lbl_name)
        end
  in
  check [] fields

let validate_facades ~disciplines fields =
  let* () = validate_registry fields in
  List.fold_result fields ~init:() ~f:(fun () field ->
      let declaration =
        Field_disciplines.find disciplines ~record_path:field.record_path
          ~position:field.label.lbl_pos
      in
      let* actual =
        match declaration with
        | Some declaration -> Ok declaration.kind
        | None ->
            let* attribute =
              Field_disciplines.parse_attributes field.label.lbl_attributes
            in
            Ok (Option.value attribute ~default:Field_disciplines.Ordinary)
      in
      let required =
        match field.kind with S.Frozen -> Field_disciplines.Frozen | Relaxed -> Relaxed
      in
      if Poly.equal actual required then Ok ()
      else
        let related =
          Option.to_list
            (Option.map declaration ~f:(fun declaration ->
                 (declaration.at, "Its field discipline is declared here")))
        in
        error ~related field.at
          (Printf.sprintf "The %s facade for %s requires [@%s]; the field is %s"
             (kind_name field.kind) field.label.lbl_name
             (Field_disciplines.attribute_name required)
             (Field_disciplines.kind_name actual)))

let resolve ~core_type ~environment ~(name : S.id) ~kind
    ~owner:((owner_pattern, owner_spec) : S.pat * S.pty) ~(selector : S.term) =
  let at = name.pid_loc in
  let rec longident = function
    | S.Qid id -> Longident.Lident id.pid_str
    | Qdot (parent, id) ->
        Longident.Ldot
          ( { txt = longident parent; loc = S.qualid_loc parent },
            { txt = id.pid_str; loc = id.pid_loc } )
  in
  let rec pattern (owner : S.pat) =
    let loc = owner.pat_loc in
    match owner.pat_desc with
    | Pid id -> Ok (id, Ast_helper.Pat.var ~loc { txt = id.pid_str; loc })
    | Pconstr (constructor, Some inner) ->
        let* receiver, inner = pattern inner in
        Ok
          ( receiver,
            Ast_helper.Pat.construct ~loc
              { txt = longident constructor; loc = S.qualid_loc constructor }
              (Some ([], inner)) )
    | Pcast (inner, typ) ->
        let* receiver, inner = pattern inner in
        Ok (receiver, Ast_helper.Pat.constraint_ ~loc inner (core_type ~at:loc typ))
    | Pwild | Ptuple _ | Pconst _ | Pconstr (_, None) ->
        error loc
          "A shared-field selector requires an owner variable or a constructor pattern \
           around one owner variable"
  in
  let* owner, owner_pattern = pattern owner_pattern in
  let* field =
    match selector.term_desc with
    | Tfield ({ term_desc = Tvar (Qid record); _ }, field)
      when String.equal record.pid_str owner.pid_str ->
        Ok field
    | _ ->
        error selector.term_loc
          "A shared-field selector must directly select a field of its owner argument"
  in
  let expression =
    let variable =
      Ast_helper.Exp.ident ~loc:owner.pid_loc
        { txt = Longident.Lident owner.pid_str; loc = owner.pid_loc }
    in
    let body =
      Ast_helper.Exp.field ~loc:selector.term_loc variable
        { txt = longident field; loc = S.qualid_loc field }
    in
    let pattern =
      Ast_helper.Pat.constraint_ ~loc:owner.pid_loc owner_pattern
        (core_type ~at:owner.pid_loc owner_spec)
    in
    Ast_helper.Exp.function_ ~loc:at
      [
        {
          Parsetree.pparam_loc = owner.pid_loc;
          pparam_desc = Pparam_val (Nolabel, None, pattern);
        };
      ]
      None (Pfunction_body body)
  in
  let* typed =
    compiler ~at (fun () ->
        let binding =
          Ast_helper.Vb.mk ~loc:at
            (Ast_helper.Pat.var ~loc:at
               { txt = Compiler_types.internal_name ~at "field_selector"; loc = at })
            expression
        in
        let structure, _, _, _, _ =
          Typemod.type_structure environment
            [ Ast_helper.Str.value ~loc:at Nonrecursive [ binding ] ]
        in
        structure)
  in
  let* receiver_pattern, record, selected, value_type =
    match typed.str_items with
    | [
     {
       str_desc =
         Tstr_value
           ( _,
             [
               {
                 vb_expr =
                   {
                     exp_desc =
                       Texp_function
                         ( [ { fp_kind = Tparam_pat argument; _ } ],
                           Tfunction_body
                             { exp_desc = Texp_field (record, _, label); exp_type; _ } );
                     _;
                   };
                 _;
               };
             ] );
       _;
     };
    ] ->
        Ok (argument, record, label, exp_type)
    | _ -> error at "The shared-field selector did not elaborate to a field access"
  in
  let* () =
    match (selected.lbl_mut, selected.lbl_atomic, selected.lbl_repres) with
    | Mutable, Nonatomic, (Record_regular | Record_inlined _) -> Ok ()
    | Immutable, _, _ -> error at "A shared-field facade requires a mutable field"
    | _, Atomic, _ ->
        error at "A shared-field facade requires an ordinary, non-atomic field"
    | _, _, (Record_float | Record_unboxed _ | Record_extension _) ->
        error at "A shared-field facade requires a boxed ordinary record field"
  in
  let* record_path =
    compiler ~at (fun () ->
        let rec normalize = function
          | Path.Pextra_ty (parent, extra) -> Path.Pextra_ty (normalize parent, extra)
          | path -> Env.normalize_type_path (Some at) record.exp_env path
        in
        normalize (Data_types.lbl_res_type_path selected))
  in
  Ok
    {
      name;
      kind;
      owner_type = receiver_pattern.pat_type;
      receiver_pattern;
      value_type;
      label = selected;
      record_path;
      at;
    }
