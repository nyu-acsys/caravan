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
  cases : bool;  (** Written with [function], whose argument a contract names. *)
  path : string list;  (** The modules it is in. *)
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

(** The parameters and body of the function [e], and whether it ends in [function] cases.
*)
let rec function_of (e : Parsetree.expression) =
  match e.pexp_desc with
  | Pexp_function (params, _, body) ->
      let names =
        List.filter_map params ~f:(fun param ->
            match param.pparam_desc with
            | Pparam_val (_, _, p) -> Some (Option.value (pattern_name p) ~default:"_")
            | Pparam_newtype _ -> None)
      in
      begin match body with
      | Pfunction_body body ->
          let inner, cases, body = function_of body in
          (names @ inner, cases, body)
      | Pfunction_cases _ -> (names, true, e)
      end
  | Pexp_newtype (_, e) | Pexp_constraint (e, _) -> function_of e
  | _ -> ([], false, e)

let definition ~path (binding : Parsetree.value_binding) =
  Option.map (pattern_name binding.pvb_pat) ~f:(fun name ->
      let parameters, cases, body = function_of binding.pvb_expr in
      { name; parameters; cases; path; body; at = binding.pvb_loc })

(** The functions that [structure] defines, in its modules and functors too. *)
let rec definitions ?(path = []) (structure : Parsetree.structure) =
  let rec module_body path (m : Parsetree.module_expr) =
    match m.pmod_desc with
    | Pmod_structure s -> definitions ~path s
    | Pmod_constraint (m, _) | Pmod_functor (_, m) -> module_body path m
    | _ -> []
  in
  List.concat_map structure ~f:(fun item ->
      match item.pstr_desc with
      | Pstr_value (_, bindings) -> List.filter_map bindings ~f:(definition ~path)
      | Pstr_module { pmb_name = { txt = Some name; _ }; pmb_expr; _ } ->
          module_body (path @ [ name ]) pmb_expr
      | _ -> [])

(** The local functions that [body] defines. *)
let local_definitions (body : Parsetree.expression) =
  let found = ref [] in
  let expr iterator (e : Parsetree.expression) =
    begin match e.pexp_desc with
    | Pexp_let (_, bindings, _) ->
        found :=
          List.rev_append (List.filter_map bindings ~f:(definition ~path:[])) !found
    | _ -> ()
    end;
    Ast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Ast_iterator.default_iterator with expr } in
  iterator.expr iterator body;
  List.rev !found

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

(** The code that an anchor writes, parsed as OCaml, with the name it is bound to if the
    anchor is [let x = e]. *)
let anchor_expression ~proof_text (anchor_loc : Location.t) =
  let text = slice proof_text anchor_loc in
  let binding = String.is_prefix (String.lstrip text) ~prefix:"let " in
  let lexbuf = Lexing.from_string (if binding then text ^ " in ()" else text) in
  Lexing.set_position lexbuf anchor_loc.loc_start;
  Lexing.set_filename lexbuf anchor_loc.loc_start.pos_fname;
  match Parse.expression lexbuf with
  | { pexp_desc = Pexp_let (_, [ vb ], _); _ } when binding ->
      begin match pattern_name vb.pvb_pat with
      | Some name -> Ok (Some name, vb.pvb_expr)
      | None -> error anchor_loc "An anchor binds a name, as let x = e"
      end
  | e -> Ok (None, e)
  | exception _ -> error anchor_loc "An anchor is an OCaml expression of the code"

(** The expressions of [e] bound to [name] by a [let]. *)
let bound_to name (e : Parsetree.expression) =
  let found = ref [] in
  let expr iterator (e : Parsetree.expression) =
    begin match e.pexp_desc with
    | Pexp_let (_, bindings, _) ->
        List.iter bindings ~f:(fun (vb : Parsetree.value_binding) ->
            if Option.equal String.equal (pattern_name vb.pvb_pat) (Some name) then
              found := vb.pvb_expr :: !found)
    | _ -> ()
    end;
    Ast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Ast_iterator.default_iterator with expr } in
  iterator.expr iterator e;
  !found

let place (loc : Location.t) =
  Printf.sprintf "%d:%d" loc.loc_start.pos_lnum
    (loc.loc_start.pos_cnum - loc.loc_start.pos_bol)

(** Where the code [e] ends, without the parentheses around it: an application ends with
    its last argument. *)
let step_end (e : Parsetree.expression) =
  match e.pexp_desc with
  | Pexp_apply (_, args) ->
      List.fold args ~init:e.pexp_loc.loc_start
        ~f:(fun last (_, (arg : Parsetree.expression)) ->
          if arg.pexp_loc.loc_end.pos_cnum > last.pos_cnum then arg.pexp_loc.loc_end
          else last)
  | _ -> e.pexp_loc.loc_end

(** The regions of [body] that may not run when it does, around each of its
    subexpressions, by location: branches, loop bodies, functions, and right operands of
    [&&] and [||]. An expression runs whenever another does if its regions are among the
    other's. *)
let regions (body : Parsetree.expression) =
  let found = ref [] in
  let rec visit regions (e : Parsetree.expression) =
    found :=
      ((e.pexp_loc.loc_start.pos_cnum, e.pexp_loc.loc_end.pos_cnum), regions) :: !found;
    let region i = (e.pexp_loc.loc_start.pos_cnum, i) :: regions in
    match e.pexp_desc with
    | Pexp_ifthenelse (c, t, f) ->
        visit regions c;
        visit (region 1) t;
        Option.iter f ~f:(visit (region 2))
    | Pexp_match (s, cases) | Pexp_try (s, cases) ->
        let s_regions = match e.pexp_desc with Pexp_try _ -> region 0 | _ -> regions in
        visit s_regions s;
        List.iteri cases ~f:(fun i (c : Parsetree.case) ->
            Option.iter c.pc_guard ~f:(visit (region (i + 1)));
            visit (region (i + 1)) c.pc_rhs)
    | Pexp_while (c, b) ->
        visit regions c;
        visit (region 1) b
    | Pexp_for (_, a, b, _, body) ->
        visit regions a;
        visit regions b;
        visit (region 1) body
    | Pexp_apply
        ( { pexp_desc = Pexp_ident { txt = Lident ("&&" | "||"); _ }; _ },
          [ (_, a); (_, b) ] ) ->
        visit regions a;
        visit (region 1) b
    | Pexp_function _ | Pexp_lazy _ -> children (region 0) e
    | _ -> children regions e
  and children regions e =
    let expr _ e = visit regions e in
    let iterator = { Ast_iterator.default_iterator with expr } in
    Ast_iterator.default_iterator.expr iterator e
  in
  visit [] body;
  !found

let regions_of regions (e : Parsetree.expression) =
  Option.value ~default:[]
    (List.Assoc.find regions
       (e.pexp_loc.loc_start.pos_cnum, e.pexp_loc.loc_end.pos_cnum)
       ~equal:Poly.equal)

(** Whether the names of the identifiers in [text] include [name]. *)
let mentions text name =
  let is_ident c = Char.is_alphanum c || Char.equal c '_' || Char.equal c '\'' in
  let n = String.length name and m = String.length text in
  let rec at i =
    match String.substr_index ~pos:i text ~pattern:name with
    | None -> false
    | Some j ->
        let before =
          j = 0 || not (is_ident text.[j - 1] || Char.equal text.[j - 1] '.')
        in
        let after = j + n >= m || not (is_ident text.[j + n]) in
        (before && after) || at (j + 1)
  in
  at 0

let within (outer : Location.t) (inner : Location.t) =
  outer.loc_start.pos_cnum <= inner.loc_start.pos_cnum
  && inner.loc_end.pos_cnum <= outer.loc_end.pos_cnum

(** The code of the step's anchor in [definition]'s body, after [previous], outside the
    local functions with outlines of their own, [excluded]. *)
let anchor_place ~proof_text definition ~excluded ~previous (anchor_loc : Location.t) =
  let* name, anchor = anchor_expression ~proof_text anchor_loc in
  let code =
    match name with
    | None -> subexpressions definition.body
    | Some name -> bound_to name definition.body
  in
  let candidates =
    List.filter code ~f:(fun e ->
        e.pexp_loc.loc_end.pos_cnum > previous
        && (not (List.exists excluded ~f:(fun at -> within at e.pexp_loc)))
        && matches anchor e)
  in
  match candidates with
  | [ e ] -> Ok e
  | [] ->
      error anchor_loc
        (Printf.sprintf "This anchor matches no code of %s after the previous step"
           definition.name)
  | candidates ->
      error anchor_loc
        (Printf.sprintf "This anchor matches %d places of %s, at %s"
           (List.length candidates) definition.name
           (String.concat ~sep:", " (List.map candidates ~f:(fun e -> place e.pexp_loc))))

(** The function that [outline] proves: the one of its name, or, if several have it, the
    one whose parameters its header names. A header's contract may rename the parameters
    of a function of its own name. *)
let definition_of definitions (outline : S.outline) =
  let name = outline.outline_name.pid_str in
  let named = List.filter definitions ~f:(fun d -> String.equal d.name name) in
  let arity d = List.length d.parameters + if d.cases then 1 else 0 in
  let params =
    Option.map outline.outline_params ~f:(List.map ~f:(fun (p : S.id) -> p.pid_str))
  in
  let same_names d params =
    List.equal String.equal d.parameters (List.take params (List.length d.parameters))
    && List.length params = arity d
  in
  match (named, params) with
  | [], _ -> error outline.outline_name.pid_loc ("The program defines no function " ^ name)
  | [ d ], None -> Ok d
  | [ d ], Some params ->
      if List.length params = arity d then Ok d
      else
        error outline.outline_name.pid_loc
          (Printf.sprintf "The function %s has %d parameter%s" name (arity d)
             (if arity d = 1 then "" else "s"))
  | _, None ->
      error outline.outline_name.pid_loc
        (Printf.sprintf
           "Several functions are named %s; list the parameters of the one this proves"
           name)
  | _, Some params ->
      begin match List.filter named ~f:(fun d -> same_names d params) with
      | [ d ] -> Ok d
      | [] ->
          error outline.outline_name.pid_loc
            (Printf.sprintf "No function %s has these parameters" name)
      | _ ->
          error outline.outline_name.pid_loc
            (Printf.sprintf "Several functions %s have these parameters" name)
      end

(** A binding of an outline that later steps may use: an export of a step, with the code
    it follows and that code's regions, or pure ghost code. *)
type binding =
  | Export of {
      key : string;
      pattern : S.pat;
      code : Parsetree.expression;
      code_regions : (int * int) list;
    }
  | Pure of { pattern : S.pat; value : S.proof_expr; text : string }

let binding_names = function
  | Export { pattern; _ } | Pure { pattern; _ } -> S.pat_names pattern

(** The bindings of [visible] that a step, at code with [regions] ending at [place], uses
    in [text], with those that the pure ones use; an export it uses must run whenever the
    step does. *)
let uses ~(visible : binding list) ~step_loc ~regions ~place text =
  let rec closure used text =
    let direct =
      List.filter visible ~f:(fun b ->
          (not (List.mem used b ~equal:phys_equal))
          && List.exists (binding_names b) ~f:(mentions text))
    in
    List.fold direct ~init:(direct @ used) ~f:(fun used b ->
        match b with Pure { text; _ } -> closure used text | Export _ -> used)
  in
  let used = closure [] text in
  let* () =
    List.fold_result used ~init:() ~f:(fun () b ->
        match b with
        | Export { code; code_regions; pattern; _ }
          when not
                 (List.is_prefix regions ~prefix:code_regions ~equal:Poly.equal
                 && (step_end code).pos_cnum <= place) ->
            error step_loc
              (Printf.sprintf
                 "The step exporting %s, at line %d of the code, does not run on every \
                  path to this step"
                 (String.concat ~sep:", " (S.pat_names pattern))
                 code.pexp_loc.loc_start.pos_lnum)
        | _ -> Ok ())
  in
  let in_order = List.filter visible ~f:(fun b -> List.mem used b ~equal:phys_equal) in
  Ok
    {
      Annotation.export = None;
      imports =
        List.filter_map in_order ~f:(function
          | Export { key; pattern; _ } -> Some (key, pattern)
          | Pure _ -> None);
      lets =
        List.filter_map in_order ~f:(function
          | Pure { pattern; value; _ } -> Some (pattern, value)
          | Export _ -> None);
    }

(** [text], written at [origin] after a [prefix] that the outline does not write, as an
    annotation at [position] of the code. *)
let synthesized ?(prefix = "") ?outline ~proof_text ~(origin : Location.t) position =
  let start = origin.loc_start in
  {
    Annotation.text = prefix ^ slice proof_text origin;
    loc = at_position position;
    origin =
      Some
        {
          position = { start with pos_cnum = start.pos_cnum - String.length prefix };
          loc = origin;
        };
    outline;
  }

(** The annotations that [outline]'s steps stand for: each step's at its place, and its
    contract and whether its proof is manual after the function. Steps other than
    linearizations make it manual. *)
let rec outline_annotations ~proof_text definitions (outline : S.outline) =
  let* definition = definition_of definitions outline in
  let locals = local_definitions definition.body in
  let nested =
    List.filter_map outline.outline_steps ~f:(function S.Nested o -> Some o | _ -> None)
  in
  let* nested_annotations =
    Result.all (List.map nested ~f:(outline_annotations ~proof_text locals))
  in
  let* excluded =
    Result.all
      (List.map nested ~f:(fun o ->
           Result.map (definition_of locals o) ~f:(fun d -> d.at)))
  in
  let regions = regions definition.body in
  let shadow visible names =
    List.filter visible ~f:(fun b ->
        not (List.exists (binding_names b) ~f:(List.mem names ~equal:String.equal)))
  in
  let* _, _, annotations =
    List.fold_result outline.outline_steps ~init:(-1, [], [])
      ~f:(fun (previous, visible, annotations) step ->
        match step with
        | S.At { anchor_loc; action; action_loc; export; _ } ->
            let* code =
              anchor_place ~proof_text definition ~excluded ~previous anchor_loc
            in
            let place = step_end code in
            let prefix =
              match action with Linearize | Initializes -> "" | Scope -> "Ghost.scope "
            in
            let* context =
              uses ~visible ~step_loc:action_loc ~regions:(regions_of regions code)
                ~place:place.pos_cnum (slice proof_text action_loc)
            in
            let key = Printf.sprintf "%d" action_loc.loc_start.pos_cnum in
            let* export =
              match (export, action) with
              | None, _ -> Ok None
              | Some pattern, Scope -> Ok (Some (key, pattern))
              | Some pattern, _ ->
                  error pattern.pat_loc "Only a scope (fun step -> e) exports a value"
            in
            let annotation =
              synthesized ~prefix ~outline:{ context with export } ~proof_text
                ~origin:action_loc place
            in
            let visible =
              match export with
              | None -> visible
              | Some (key, pattern) ->
                  Export { key; pattern; code; code_regions = regions_of regions code }
                  :: shadow visible (S.pat_names pattern)
            in
            Ok (place.pos_cnum, visible, annotation :: annotations)
        | On_return { return_loc } ->
            let place = definition.body.pexp_loc.loc_end in
            let* outline =
              uses ~visible ~step_loc:return_loc ~regions:[] ~place:place.pos_cnum
                (slice proof_text return_loc)
            in
            let annotation =
              synthesized ~prefix:"proof " ~outline ~proof_text ~origin:return_loc place
            in
            Ok (previous, visible, annotation :: annotations)
        | Let { pattern; value } ->
            let binding =
              Pure { pattern; value; text = slice proof_text value.proof_loc }
            in
            Ok (previous, binding :: shadow visible (S.pat_names pattern), annotations)
        | Nested _ -> Ok (previous, visible, annotations))
  in
  let after = definition.at.loc_end in
  let manual =
    if
      List.exists outline.outline_steps ~f:(function
        | S.At { action = Linearize; _ } | Let _ -> false
        | At _ | On_return _ | Nested _ -> true)
    then
      [
        {
          Annotation.text = "manual";
          loc = at_position after;
          origin = None;
          outline = None;
        };
      ]
    else []
  in
  let contract =
    Option.to_list
      (Option.map outline.outline_contract ~f:(fun origin ->
           synthesized ~proof_text ~origin after))
  in
  Ok (List.rev annotations @ List.concat nested_annotations @ manual @ contract)

(** The outlines of [declarations], in their modules, with the modules' path. *)
let rec module_outlines path (declarations : S.proof_decl list) =
  List.concat_map declarations ~f:(function
    | S.Proof_module { module_name; module_declarations; module_outlines = outlines; _ }
    | Proof_definition { module_name; module_declarations; module_outlines = outlines; _ }
      ->
        let path = path @ [ module_name.pid_str ] in
        List.map outlines ~f:(fun o -> (path, o))
        @ module_outlines path module_declarations
    | _ -> [])

(** The annotations that the outlines of [proof] stand for in [structure], each in the
    source module of its proof module. A program with outlines has no proof annotations of
    its own among [annotations]. *)
let annotations ~proof_text ~(structure : Parsetree.structure) ~annotations
    (proof : S.proof_file) =
  let outlines =
    List.map proof.outlines ~f:(fun o -> ([], o)) @ module_outlines [] proof.declarations
  in
  let* () =
    let proof (a : Annotation.t) =
      match Annotation.kind a with
      | Ghost | Scope | Returns | Proof | Manual | Linearization | Initializes -> true
      | Contract | Loop | Predicate | Ghost_module | Initially | Trusted -> false
    in
    match (outlines, List.filter annotations ~f:proof) with
    | _ :: _, (first : Annotation.t) :: _ ->
        error first.loc
          "A program whose proofs are outlines in its .proof file has no proof \
           annotations"
    | _ -> Ok ()
  in
  let key (path, (o : S.outline)) =
    ( path,
      o.outline_name.pid_str,
      Option.map o.outline_params ~f:(List.map ~f:(fun (p : S.id) -> p.pid_str)) )
  in
  let* (_ : (string list * S.outline) list) =
    List.fold_result outlines ~init:[] ~f:(fun seen ((_, outline) as entry) ->
        if List.exists seen ~f:(fun o -> Poly.equal (key o) (key entry)) then
          error outline.outline_name.pid_loc "This function has another outline"
        else Ok (entry :: seen))
  in
  let definitions = definitions structure in
  let* annotations =
    Result.all
      (List.map outlines ~f:(fun (path, outline) ->
           outline_annotations ~proof_text
             (List.filter definitions ~f:(fun d -> List.equal String.equal d.path path))
             outline))
  in
  Ok (List.concat annotations)
