(** Proof outlines: the proofs of functions in the [.proof] file, as steps at places in
    their code. Each step becomes the annotation it stands for, at its place. *)

open Base
open Caravan_spec
module S = Spec_ast

let ( let* ) = Result.( >>= )
let error loc message = Error (Report.error Type loc message)

type definition = {
  name : string;
  parameters : string list;
  body : Parsetree.expression;
  at : Location.t;
}
(** A function of the program: its name, parameter names, and body. *)

(** The name of a parameter bound by a variable, as [x] or [(x : t)]. *)
let rec pattern_name (p : Parsetree.pattern) =
  match p.ppat_desc with
  | Ppat_var x -> Some x.txt
  | Ppat_constraint (p, _) -> pattern_name p
  | _ -> None

let rec function_of (e : Parsetree.expression) =
  match e.pexp_desc with
  | Pexp_function (params, _, Pfunction_body body) ->
      let names =
        List.filter_map params ~f:(fun param ->
            match param.pparam_desc with
            | Pparam_val (_, _, p) -> Some (Option.value (pattern_name p) ~default:"_")
            | Pparam_newtype _ -> None)
      in
      let inner, body = function_of body in
      (names @ inner, body)
  | Pexp_function (_, _, Pfunction_cases _) -> ([], e)
  | Pexp_newtype (_, e) | Pexp_constraint (e, _) -> function_of e
  | _ -> ([], e)

(** The functions that [structure] defines, in its modules too. *)
let rec definitions (structure : Parsetree.structure) =
  List.concat_map structure ~f:(fun item ->
      match item.pstr_desc with
      | Pstr_value (_, bindings) ->
          List.filter_map bindings ~f:(fun binding ->
              Option.map (pattern_name binding.pvb_pat) ~f:(fun name ->
                  let parameters, body = function_of binding.pvb_expr in
                  { name; parameters; body; at = binding.pvb_loc }))
      | Pstr_module { pmb_expr = { pmod_desc = Pmod_structure s; _ }; _ } -> definitions s
      | _ -> [])

(** [e] with its applications flattened and [@@] and [|>] as applications. *)
let rec application (e : Parsetree.expression) =
  match e.pexp_desc with
  | Pexp_apply
      ( { pexp_desc = Pexp_ident { txt = Lident "@@"; _ }; _ },
        [ (Nolabel, f); (Nolabel, x) ] ) ->
      let f, args = application f in
      (f, args @ [ (Asttypes.Nolabel, x) ])
  | Pexp_apply
      ( { pexp_desc = Pexp_ident { txt = Lident "|>"; _ }; _ },
        [ (Nolabel, x); (Nolabel, f) ] ) ->
      let f, args = application f in
      (f, args @ [ (Asttypes.Nolabel, x) ])
  | Pexp_apply (f, args) ->
      let f, inner = application f in
      (f, inner @ args)
  | _ -> (e, [])

(** Whether the code [e] is what the anchor [a] writes, modulo formatting, parentheses and
    [@@] and [|>]. *)
let rec matches (a : Parsetree.expression) (e : Parsetree.expression) =
  let a_head, a_args = application a and e_head, e_args = application e in
  if not (List.is_empty a_args && List.is_empty e_args) then
    (not (List.is_empty a_args))
    && List.length a_args = List.length e_args
    && matches a_head e_head
    && List.for_all2_exn a_args e_args ~f:(fun (la, a) (le, e) ->
        Poly.equal la le && matches a e)
  else
    match (a.pexp_desc, e.pexp_desc) with
    | Pexp_ident a, Pexp_ident e ->
        Poly.equal (Longident.flatten a.txt) (Longident.flatten e.txt)
    | Pexp_constant a, Pexp_constant e -> Poly.equal a.pconst_desc e.pconst_desc
    | Pexp_construct (a, None), Pexp_construct (e, None) ->
        Poly.equal (Longident.flatten a.txt) (Longident.flatten e.txt)
    | Pexp_construct (a, Some x), Pexp_construct (e, Some y) ->
        Poly.equal (Longident.flatten a.txt) (Longident.flatten e.txt) && matches x y
    | Pexp_tuple a, Pexp_tuple e ->
        List.length a = List.length e
        && List.for_all2_exn a e ~f:(fun (la, a) (le, e) ->
            Poly.equal la le && matches a e)
    | Pexp_field (a, fa), Pexp_field (e, fe) ->
        Poly.equal (Longident.flatten fa.txt) (Longident.flatten fe.txt) && matches a e
    | Pexp_constraint (a, _), _ -> matches a e
    | _, Pexp_constraint (e, _) -> matches a e
    | _ -> false

(** The subexpressions of [e]. *)
let subexpressions (e : Parsetree.expression) =
  let found = ref [] in
  let expr iterator e =
    found := e :: !found;
    Ast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Ast_iterator.default_iterator with expr } in
  iterator.expr iterator e;
  List.rev !found

let slice text (loc : Location.t) =
  String.sub text ~pos:loc.loc_start.pos_cnum
    ~len:(loc.loc_end.pos_cnum - loc.loc_start.pos_cnum)

(** An empty location at [position] of the code, where an annotation would start. *)
let at_position (position : Lexing.position) =
  { Location.loc_start = position; loc_end = position; loc_ghost = true }

(** The code that the anchor [anchor] writes, parsed as OCaml. *)
let anchor_expression ~proof_text (anchor_loc : Location.t) =
  let lexbuf = Lexing.from_string (slice proof_text anchor_loc) in
  Lexing.set_position lexbuf anchor_loc.loc_start;
  Lexing.set_filename lexbuf anchor_loc.loc_start.pos_fname;
  try Ok (Parse.expression lexbuf)
  with _ -> error anchor_loc "An anchor is an OCaml expression of the code"

let place (loc : Location.t) =
  Printf.sprintf "%d:%d" loc.loc_start.pos_lnum
    (loc.loc_start.pos_cnum - loc.loc_start.pos_bol)

(** The place of the step's anchor in [definition]'s body, after [previous]. *)
let anchor_place ~proof_text definition ~previous (anchor_loc : Location.t) =
  let* anchor = anchor_expression ~proof_text anchor_loc in
  let candidates =
    List.filter (subexpressions definition.body) ~f:(fun e ->
        e.pexp_loc.loc_end.pos_cnum > previous && matches anchor e)
  in
  match candidates with
  | [ e ] -> Ok e.pexp_loc.loc_end
  | [] ->
      error anchor_loc
        (Printf.sprintf "This anchor matches no code of %s after the previous step"
           definition.name)
  | candidates ->
      error anchor_loc
        (Printf.sprintf "This anchor matches %d places of %s, at %s"
           (List.length candidates) definition.name
           (String.concat ~sep:", " (List.map candidates ~f:(fun e -> place e.pexp_loc))))

(** The function that [outline] proves. *)
let definition_of definitions (outline : S.outline) =
  let name = outline.outline_name.pid_str in
  let named = List.filter definitions ~f:(fun d -> String.equal d.name name) in
  let selected =
    match outline.outline_params with
    | None -> named
    | Some params ->
        List.filter named ~f:(fun d ->
            List.equal String.equal d.parameters
              (List.map params ~f:(fun (p : S.id) -> p.pid_str)))
  in
  match (named, selected) with
  | [], _ -> error outline.outline_name.pid_loc ("The program defines no function " ^ name)
  | _, [ d ] -> Ok d
  | _, [] ->
      error outline.outline_name.pid_loc
        (Printf.sprintf "No function %s has these parameters" name)
  | _, _ ->
      error outline.outline_name.pid_loc
        (Printf.sprintf
           "Several functions are named %s; list the parameters of the one this proves"
           name)

(** The annotations that [outline]'s steps stand for. *)
let outline_annotations ~proof_text definitions (outline : S.outline) =
  let* definition = definition_of definitions outline in
  let* _, annotations =
    List.fold_result outline.outline_steps ~init:(-1, [])
      ~f:(fun (previous, annotations) step ->
        match step with
        | S.At { anchor_loc; action_loc; _ } ->
            let* place = anchor_place ~proof_text definition ~previous anchor_loc in
            let annotation =
              {
                Annotation.text = slice proof_text action_loc;
                loc = at_position place;
                origin = Some action_loc.loc_start;
              }
            in
            Ok (place.pos_cnum, annotation :: annotations)
        | On_return { return_loc } ->
            (* A proof annotation after the body, its keyword before the step's code. *)
            let keyword = "proof " in
            let start = return_loc.loc_start in
            let annotation =
              {
                Annotation.text = keyword ^ slice proof_text return_loc;
                loc = at_position definition.body.pexp_loc.loc_end;
                origin =
                  Some { start with pos_cnum = start.pos_cnum - String.length keyword };
              }
            in
            Ok (previous, annotation :: annotations))
  in
  Ok (List.rev annotations)

(** The annotations that [outlines] stand for in [structure]. A program with outlines has
    no annotations of its own: [annotations]. *)
let annotations ~proof_text ~(structure : Parsetree.structure) ~annotations
    (outlines : S.outline list) =
  let* () =
    match (outlines, annotations) with
    | _ :: _, (first : Annotation.t) :: _ ->
        error first.loc
          "A program whose proofs are outlines in its .proof file has no annotations"
    | _ -> Ok ()
  in
  let key (o : S.outline) =
    ( o.outline_name.pid_str,
      Option.map o.outline_params ~f:(List.map ~f:(fun (p : S.id) -> p.pid_str)) )
  in
  let* (_ : S.outline list) =
    List.fold_result outlines ~init:[] ~f:(fun seen outline ->
        if List.exists seen ~f:(fun o -> Poly.equal (key o) (key outline)) then
          error outline.outline_name.pid_loc "This function has another outline"
        else Ok (outline :: seen))
  in
  let definitions = definitions structure in
  let* annotations =
    Result.all (List.map outlines ~f:(outline_annotations ~proof_text definitions))
  in
  Ok (List.concat annotations)
