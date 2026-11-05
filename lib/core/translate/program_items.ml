(** The items of a program: data types, functions, local functions, shared structures and
    their members, and forwarding for checked views. *)

open Base
open Translate_context
open Spec_terms
open Proof_terms
open Atomic_proofs
open Procedures

let binding_name_location (binding : Typedtree.value_binding) =
  match binding.vb_pat.pat_desc with
  | Tpat_var (_, name, _) -> name.loc
  | _ -> binding.vb_pat.pat_loc

(** The data types and functions of [structure], in order, with the contracts of the
    functions in [annotations], or in [interface], by their names. *)
let items ?(libraries = []) (source : Source.t) (inventory : Module_inventory.t) =
  let* signature_predicates =
    all
      (List.filter inventory.constraints ~f:(fun constraint_ ->
           Option.is_some constraint_.Module_inventory.owner))
      ~f:(fun constraint_ ->
        all constraint_.Module_inventory.signature.signature_resources
          ~f:(fun (name, resource) ->
            let environment = Source.annotation_env source resource.site.environment in
            let* parameters =
              Proof_bindings.parameter_types environment resource.declaration.pred_params
            in
            Ok
              (List.map constraint_.signature.signature_values ~f:(fun (_, value) ->
                   let parameters =
                     Compiler_types.map_group parameters ~f:(fun typ ->
                         Subst.type_expr value.origin_projection
                           (Subst.type_expr resource.substitution typ))
                   in
                   (value.declaration.val_id, name, parameters)))))
  in
  let signature_predicates = List.concat (List.concat signature_predicates) in
  let* data =
    all inventory.types ~f:(fun (entry : Module_inventory.type_definition) ->
        let* data = Datatypes.of_declaration entry.declaration in
        let data = Datatypes.with_paths data entry.paths in
        let base = String.concat ~sep:"_" (entry.namespace @ [ data.module_name ]) in
        let data = Datatypes.with_name data (Fresh_names.fresh base) in
        let heap =
          Option.map data.heap
            ~f:
              (List.map ~f:(fun (field : Datatypes.field) ->
                   { field with raven_field = Fresh_names.fresh field.raven_field }))
        in
        Ok { data with heap })
  in
  let* library = Exceptions.library_declared source.env libraries in
  let* exceptions = Exceptions.datatype ~library inventory.structure in
  let data = data @ Option.to_list exceptions in
  let same_scope (a : Module_inventory.value) (b : Module_inventory.value) =
    let a = a.site.scope.location and b = b.site.scope.location in
    a.loc_start.pos_cnum = b.loc_start.pos_cnum && a.loc_end.pos_cnum = b.loc_end.pos_cnum
  in
  let function_type (entry : Module_inventory.value) =
    let rec arrow typ =
      match
        Types.get_desc (Ctype.expand_head entry.Module_inventory.site.environment typ)
      with
      | Tarrow _ -> true
      | Tpoly (body, []) -> arrow body
      | _ -> false
    in
    arrow entry.binding.vb_pat.pat_type
  in
  let* functions =
    List.fold_result inventory.values ~init:[]
      ~f:(fun functions (entry : Module_inventory.value) ->
        let vb = entry.binding in
        match (vb.vb_pat.pat_desc, function_parts vb.vb_expr) with
        | Tpat_var (id, _, _), Some (params, body) ->
            let site = entry.site in
            let* own =
              contract_with_origin_after ~scope:site.scope site.annotations
                ~item_loc:site.item_loc ~next:site.next
            in
            let* supplied =
              all entry.signatures ~f:(fun (view : Module_inventory.signature_value) ->
                  let site = view.site in
                  let* contract =
                    contract_with_origin_after ~scope:site.scope site.annotations
                      ~item_loc:site.item_loc ~next:site.next
                  in
                  let* () =
                    match contract with
                    | None -> Ok ()
                    | Some (contract, _) ->
                        let* () =
                          Signature_contract.lowerable source view
                            ~environment:
                              (Source.annotation_env source entry.site.environment)
                            contract
                        in
                        Signature_contract.check
                          ~predicates:(function
                            | S.Qid id ->
                                List.find_map signature_predicates
                                  ~f:(fun (value, name, parameters) ->
                                    Option.some_if
                                      (Ident.same value view.declaration.val_id
                                      && String.equal name id.pid_str)
                                      parameters)
                            | Qdot _ -> None)
                          ~restricted:(not (List.is_empty entry.namespace))
                          ~logical_types:source.Source.logical_types source view contract
                  in
                  Ok (Option.map contract ~f:(fun contract -> (contract, site.item_loc))))
            in
            let supplied = List.filter_opt supplied in
            let* contract =
              match (own, supplied) with
              | Some _, (_, at) :: _ ->
                  let root = List.is_empty entry.namespace in
                  error vb.vb_loc
                    ~related:
                      [
                        ( at,
                          if root then "Its contract in the interface"
                          else "Its contract in the signature" );
                      ]
                    (if root then
                       Printf.sprintf
                         "%s has a contract in its interface and another one here"
                         (Ident.name id)
                     else
                       "A function has a contract in its signature and another one here")
              | None, (contract, _) :: [] -> Ok (Some contract)
              | None, [] -> Ok None
              | Some _, []
                when (not (List.is_empty entry.signatures))
                     && not (List.is_empty entry.namespace) ->
                  error vb.vb_loc
                    "An exported module member's contract must be declared in its \
                     signature"
              | Some contract, [] -> Ok (Some contract)
              | None, _ :: (_, at) :: _ ->
                  error at "Multiple contracts for a module member are unsupported"
            in
            let contract_origin = Option.map contract ~f:snd in
            let contract = Option.map contract ~f:fst in
            let earlier =
              List.take_while inventory.values ~f:(fun other ->
                  not (phys_equal other entry))
            in
            let later = List.drop inventory.values (List.length earlier + 1) in
            let same_name other =
              same_scope entry other
              &&
              match other.Module_inventory.binding.vb_pat.pat_desc with
              | Tpat_var (other, _, _) -> String.equal (Ident.name id) (Ident.name other)
              | _ -> false
            in
            let base =
              if List.is_empty entry.namespace && List.exists later ~f:same_name then
                Printf.sprintf "%s_%d" (Ident.name id)
                  (1 + List.count earlier ~f:same_name)
              else
                String.uncapitalize
                  (String.concat ~sep:"_" (entry.namespace @ [ Ident.name id ]))
            in
            let base = String.map base ~f:(function '.' -> '_' | c -> c) in
            Ok
              ({
                 id;
                 namespace = entry.namespace;
                 paths = entry.paths;
                 environment =
                   Source.annotation_env source ~at:site.item_loc site.environment;
                 signature_sites = entry.signatures;
                 scheme_type = vb.vb_pat.pat_type;
                 source_scheme = None;
                 lexical_owner = None;
                 raven_name = Fresh_names.fresh base;
                 params;
                 body;
                 loc = vb.vb_loc;
                 name_loc = binding_name_location vb;
                 contract;
                 contract_origin;
                 next =
                   Some
                     (Option.value site.next
                        ~default:
                          {
                            site.scope.location with
                            loc_start = site.scope.location.loc_end;
                          });
                 prefix = [];
                 prefix_count = 0;
                 captured = [];
                 role = None;
                 copy_for = None;
                 manual =
                   manual_after ~scope:site.scope site.annotations ~item_loc:site.item_loc
                     ~next:site.next;
                 trusted =
                   trusted_after ~scope:site.scope site.annotations
                     ~item_loc:site.item_loc ~next:site.next;
               }
              :: functions)
        | Tpat_var _, None when function_type entry ->
            begin match vb.vb_expr.exp_desc with
            | Texp_ident (path, _, _) ->
                let* contracts =
                  let site = entry.site in
                  let* own =
                    contract_after ~scope:site.scope site.annotations
                      ~item_loc:site.item_loc ~next:site.next
                  in
                  let* supplied =
                    all entry.signatures
                      ~f:(fun (view : Module_inventory.signature_value) ->
                        let site = view.site in
                        contract_after ~scope:site.scope site.annotations
                          ~item_loc:site.item_loc ~next:site.next)
                  in
                  Ok (own :: supplied)
                in
                let* () =
                  if List.exists contracts ~f:Option.is_some then
                    unsupported vb.vb_loc "Contracts on function value aliases"
                  else Ok ()
                in
                let* path =
                  Source.normalize_value_path entry.site.environment
                    ~at:vb.vb_expr.exp_loc path
                in
                begin match
                  List.find functions ~f:(fun target ->
                      List.mem target.paths path ~equal:Path.same)
                with
                | None ->
                    unsupported vb.vb_loc
                      "A function value alias that does not refer to an earlier \
                       translated function"
                | Some target ->
                    let paths =
                      List.fold entry.paths ~init:target.paths ~f:(fun paths path ->
                          if List.mem paths path ~equal:Path.same then paths
                          else paths @ [ path ])
                    in
                    Ok
                      (List.map functions ~f:(fun function_ ->
                           if phys_equal function_ target then { function_ with paths }
                           else function_))
                end
            | _ -> unsupported vb.vb_loc "This definition"
            end
        | _ -> unsupported vb.vb_loc "This definition")
  in
  Ok (data, List.rev functions)

(** The identifiers that [e] refers to by a name of its own. *)
let referenced (e : Typedtree.expression) : Ident.t list =
  let found = ref [] in
  let expr iterator (e : Typedtree.expression) =
    begin match e.exp_desc with
    | Texp_ident (Pident id, _, _) -> found := id :: !found
    | _ -> ()
    end;
    Tast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Tast_iterator.default_iterator with expr } in
  iterator.expr iterator e;
  !found

(** An iterator collecting the identifiers that patterns bind, and what it found. *)
let binders () =
  let found = ref [] in
  let pat : type k. Tast_iterator.iterator -> k Typedtree.general_pattern -> unit =
   fun iterator p ->
    begin match p.pat_desc with
    | Tpat_var (id, _, _) | Tpat_alias (_, id, _, _, _) ->
        found := (id, p.pat_type, p.pat_loc) :: !found
    | _ -> ()
    end;
    Tast_iterator.default_iterator.pat iterator p
  in
  ({ Tast_iterator.default_iterator with pat }, found)

(** The identifiers that the patterns of [e] bind, with their types and locations. *)
let typed_bound_in (e : Typedtree.expression) =
  let iterator, found = binders () in
  iterator.expr iterator e;
  !found

(** The identifiers that the patterns of [e] bind, its functions' parameters included. *)
let bound_in (e : Typedtree.expression) : Ident.t list =
  List.map (typed_bound_in e) ~f:(fun (id, _, _) -> id)

(** The identifiers that the parameters [params] bind, in order. *)
let params_bound (params : Typedtree.function_param list) : Ident.t list =
  let iterator, found = binders () in
  List.iter params ~f:(fun p ->
      match p.fp_kind with
      | Tparam_pat pat -> iterator.pat iterator pat
      | Tparam_optional_default (pat, _) -> iterator.pat iterator pat);
  List.rev_map !found ~f:(fun (id, _, _) -> id)

(** The local functions of the top-level function [outer], lifted to the top level, with
    their contracts in [annotations]: one after the function's definition, before the
    expression it is local to. A function that [continues] [outer] takes [outer]'s
    parameters first and has its contract too; another may not use [outer]'s variables. *)
let local_functions ~source (outer : func) (annotations : Annotation.t list) =
  let found = ref [] in
  let expr iterator (e : Typedtree.expression) =
    begin match e.exp_desc with
    | Texp_let (_, [ vb ], rest) ->
        begin match (vb.vb_pat.pat_desc, function_parts vb.vb_expr) with
        | Tpat_var (id, _, _), Some (params, body) ->
            found := (vb, id, params, body, rest) :: !found
        | _ -> ()
        end
    | _ -> ()
    end;
    Tast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Tast_iterator.default_iterator with expr } in
  iterator.expr iterator outer.body;
  let outer_params = params_bound outer.params in
  let outer_bound = outer_params @ bound_in outer.body in
  all (List.rev !found)
    ~f:(fun
        ((vb : Typedtree.value_binding), id, params, body, (rest : Typedtree.expression))
      ->
      let* contract =
        contract_with_origin_after annotations ~item_loc:vb.vb_loc
          ~next:(Some rest.exp_loc)
      in
      let contract_origin = Option.map contract ~f:snd in
      let contract = Option.map contract ~f:fst in
      let continues = Option.bind contract ~f:(fun c -> c.continues) in
      let* () =
        match continues with
        | Some g when not (String.equal g.pid_str (Ident.name outer.id)) ->
            error g.pid_loc
              (Printf.sprintf "A local function of %s continues %s only"
                 (Ident.name outer.id) (Ident.name outer.id))
        | _ -> Ok ()
      in
      let prefix = if Option.is_some continues then outer_params else [] in
      let own = (id :: params_bound params) @ bound_in body in
      let captured =
        List.filter (referenced body) ~f:(fun x ->
            List.mem outer_bound x ~equal:Ident.same
            && (not (List.mem own x ~equal:Ident.same))
            && not (List.mem prefix x ~equal:Ident.same))
      in
      (* The variables of its context that the function uses are parameters of it. *)
      let captured = List.dedup_and_sort captured ~compare:Ident.compare in
      let typed =
        let iterator, found = binders () in
        List.iter outer.params ~f:(fun p ->
            match p.fp_kind with
            | Tparam_pat pat -> iterator.pat iterator pat
            | Tparam_optional_default (pat, _) -> iterator.pat iterator pat);
        !found @ typed_bound_in outer.body
      in
      let* captured_params =
        all captured ~f:(fun x ->
            match List.find typed ~f:(fun (y, _, _) -> Ident.same x y) with
            | Some (_, t, at) ->
                let uid = Shape.Uid.internal_not_actually_unique in
                let pattern : Typedtree.pattern =
                  {
                    pat_desc = Tpat_var (x, Location.mkloc (Ident.name x) at, uid);
                    pat_loc = at;
                    pat_extra = [];
                    pat_type = t;
                    pat_env = body.exp_env;
                    pat_attributes = [];
                  }
                in
                Ok
                  {
                    Typedtree.fp_arg_label = Nolabel;
                    fp_param = x;
                    fp_partial = Total;
                    fp_kind = Tparam_pat pattern;
                    fp_newtypes = [];
                    fp_loc = at;
                  }
            | None ->
                error vb.vb_loc
                  (Printf.sprintf
                     "The type of %s, which this local function uses, is unknown"
                     (Ident.name x)))
      in
      let captured_names =
        List.map captured ~f:(fun x -> S.Lvar (S.mk_id ~loc:vb.vb_loc (Ident.name x)))
      in
      (* The contract of the function continued, with its parameters first. *)
      let contract =
        match (contract, continues, outer.contract) with
        | Some c, Some _, Some oc ->
            let names (f_params : Typedtree.function_param list) (h : S.header option) =
              match h with
              | Some h -> h.hd_args
              | None ->
                  List.map f_params ~f:(fun p ->
                      match p.fp_kind with
                      | Tparam_pat { pat_desc = Tpat_var (x, _, _); pat_loc; _ } ->
                          S.Lvar (S.mk_id ~loc:pat_loc (Ident.name x))
                      | _ -> S.Lwild)
            in
            let header =
              {
                S.hd_name = S.mk_id ~loc:vb.vb_loc (Ident.name id);
                hd_ret =
                  Option.value_map c.header ~default:[ S.Lwild ] ~f:(fun h -> h.hd_ret);
                hd_args =
                  names outer.params oc.header @ captured_names @ names params c.header;
              }
            in
            Some
              {
                c with
                header = Some header;
                atomic = oc.atomic;
                requires = oc.requires @ c.requires;
                atomic_requires = oc.atomic_requires;
                atomic_ensures = oc.atomic_ensures;
              }
        | Some c, None, _ ->
            (* Its own contract, which names the variables it uses as they are named. *)
            Some
              (match c.header with
              | Some h ->
                  { c with header = Some { h with hd_args = captured_names @ h.hd_args } }
              | None -> c)
        | _ -> contract
      in
      let prefix_params = if Option.is_some continues then outer.params else [] in
      Ok
        {
          id;
          namespace = outer.namespace;
          paths = [ Path.Pident id ];
          environment = Source.annotation_env source ~at:rest.exp_loc rest.exp_env;
          signature_sites = [];
          scheme_type = vb.vb_pat.pat_type;
          source_scheme = None;
          lexical_owner = Some outer.id;
          raven_name = outer.raven_name ^ "$local$" ^ Ident.name id;
          params = prefix_params @ captured_params @ params;
          body;
          loc = vb.vb_loc;
          name_loc = binding_name_location vb;
          contract;
          contract_origin;
          next = Some rest.exp_loc;
          prefix;
          prefix_count = List.length prefix_params;
          captured;
          manual =
            outer.manual
            || manual_after annotations ~item_loc:vb.vb_loc ~next:(Some rest.exp_loc);
          trusted =
            trusted_after annotations ~item_loc:vb.vb_loc ~next:(Some rest.exp_loc);
          role = Option.map continues ~f:(fun _ -> outer.id);
          copy_for = None;
        })

(** The offsets of the ends of the applications of [Atomic]'s operations in [structure].
*)
let atomic_steps (structure : Typedtree.structure) : int list =
  let found = ref [] in
  let expr iterator (e : Typedtree.expression) =
    begin match e.exp_desc with
    | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _)
      when Option.is_some (atomic_name path) ->
        found := step_end e :: !found
    | _ -> ()
    end;
    Tast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Tast_iterator.default_iterator with expr } in
  iterator.structure iterator structure;
  !found

(** Resolves annotations to one source expression, including nested calls. *)
let attached_annotations ?(all_expressions = false) ?(innermost = false)
    (source : Source.t) typed annotations ~kind ~is_target ~description =
  let attached =
    List.filter_map annotations ~f:(fun a ->
        if Poly.equal (Annotation.kind a) kind then
          let rec anchor i =
            if i > 0 && Char.is_whitespace source.text.[i - 1] then anchor (i - 1)
            else
              match
                List.find source.comments ~f:(fun (_, at) ->
                    at.Location.loc_end.pos_cnum = i)
              with
              | Some (_, at) -> anchor at.loc_start.pos_cnum
              | None -> i
          in
          Some (anchor a.loc.loc_start.pos_cnum, a)
        else None)
  in
  let expressions = ref [] in
  let collect_expression iterator (e : Typedtree.expression) =
    let eligible = is_target e in
    if all_expressions then
      begin if eligible then expressions := (e, true) :: !expressions
      end
    else
      begin match e.exp_desc with
      | Texp_apply _ | Texp_record _ -> expressions := (e, eligible) :: !expressions
      | _ -> ()
      end;
    Tast_iterator.default_iterator.expr iterator e
  in
  let iterator = { Tast_iterator.default_iterator with expr = collect_expression } in
  iterator.structure iterator typed;
  let* attached =
    all attached ~f:(fun (anchor, annotation) ->
        let candidates =
          List.filter !expressions ~f:(fun (e, _) ->
              (anchor = step_end e
              &&
              match e.exp_desc with
              | Texp_apply (callee, _) -> anchor >= callee.exp_loc.loc_end.pos_cnum
              | _ -> true)
              || anchor = e.exp_loc.loc_end.pos_cnum
              || List.exists e.exp_extra ~f:(fun (_, at, _) ->
                  anchor = at.loc_end.pos_cnum))
        in
        match
          List.min_elt candidates ~compare:(fun (a, _) (b, _) ->
              match
                Int.compare a.exp_loc.loc_start.pos_cnum b.exp_loc.loc_start.pos_cnum
              with
              | 0 -> Int.compare b.exp_loc.loc_end.pos_cnum a.exp_loc.loc_end.pos_cnum
              | order -> if innermost then -order else order)
        with
        | None | Some (_, false) -> error annotation.loc description
        | Some (expression, true) ->
            Ok
              ( ( expression.exp_loc.loc_start.pos_cnum,
                  expression.exp_loc.loc_end.pos_cnum ),
                annotation ))
  in
  let* () =
    match List.find_a_dup (List.map attached ~f:fst) ~compare:Poly.compare with
    | None -> Ok ()
    | Some start ->
        let annotation = List.Assoc.find_exn attached start ~equal:Poly.equal in
        error annotation.loc "This expression has more than one annotation of this kind"
  in
  Ok attached

let initialization_annotations source typed annotations =
  let is_target (e : Typedtree.expression) =
    match e.exp_desc with
    | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _) ->
        Option.exists (stdlib_name path) ~f:(String.equal "ref")
        || Option.exists (atomic_name path) ~f:(fun op ->
            List.mem [ "make"; "make_contended" ] op ~equal:String.equal)
    | Texp_record { fields; extended_expression = None; _ } ->
        Array.exists fields ~f:(fun (label, _) ->
            Poly.equal label.Data_types.lbl_mut Mutable)
    | _ -> false
  in
  attached_annotations source typed annotations ~kind:Annotation.Initializes ~is_target
    ~description:"This annotation must follow a fresh allocation"

let access_annotations ~libraries ?(checked = []) source typed annotations ~functions =
  let functions =
    Path_bindings.of_list
      (List.concat_map functions ~f:(fun f ->
           List.map f.paths ~f:(fun path -> (path, ()))))
  in
  let functions =
    List.fold checked ~init:functions ~f:(fun functions path ->
        Path_bindings.add functions path ())
  in
  let libraries = library_calls libraries in
  let is_target (e : Typedtree.expression) =
    match e.exp_desc with
    | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _) -> (
        Option.exists (atomic_name path) ~f:(fun op ->
            not (String.is_prefix op ~prefix:"make"))
        ||
        match Source.normalize_value_path e.exp_env ~at:e.exp_loc path with
        | Ok path -> Path_bindings.mem functions path || Path_bindings.mem libraries path
        | Error _ -> false)
    | _ -> false
  in
  attached_annotations source typed annotations ~kind:Annotation.Scope ~is_target
    ~description:"Ghost.scope must follow an Atomic access or a checked procedure call"

(** The functions of [funcs] that must be pure: those that contracts call or say are
    [pure], and the functions these call. *)
let pure_functions (funcs : func list) =
  let* () =
    Result.all_unit
      (List.map funcs ~f:(fun f ->
           let clauses =
             Option.value_map f.contract ~default:[] ~f:(fun (c : S.contract) ->
                 c.requires @ c.ensures @ c.atomic_requires @ c.atomic_ensures @ c.variant)
           in
           Result.all_unit
             (List.map clauses ~f:(fun term ->
                  Result.all_unit
                    (List.map
                       (term_references (contract_bound_names f) term)
                       ~f:(fun q ->
                         match Source.value_path f.environment q with
                         | Some (Path.Pdot _ as path)
                           when List.exists funcs ~f:(fun target ->
                                    (not (List.is_empty target.signature_sites))
                                    && List.mem target.paths path ~equal:Path.same) ->
                             unsupported term.term_loc
                               "A specification call through a constrained module \
                                signature"
                         | Some _ | None -> Ok ()))))))
  in
  let referenced_in_contracts =
    List.concat_map funcs ~f:(fun f ->
        Option.value_map f.contract ~default:[] ~f:(fun (c : S.contract) ->
            List.concat_map
              (c.requires @ c.ensures @ c.variant)
              ~f:(fun t ->
                List.filter_map
                  (term_references (contract_bound_names f) t)
                  ~f:(Source.value_path f.environment))))
  in
  let seeds =
    List.filter funcs ~f:(fun f ->
        List.exists f.paths ~f:(fun path ->
            List.mem referenced_in_contracts path ~equal:Path.same)
        || Option.exists f.contract ~f:(fun (c : S.contract) -> c.pure))
  in
  let is_in set f = List.exists set ~f:(fun g -> Ident.same g.id f.id) in
  let references body =
    let paths = ref [] in
    let expr iterator (e : Typedtree.expression) =
      (match e.exp_desc with
      | Texp_ident (path, _, _) -> paths := (e.exp_env, e.exp_loc, path) :: !paths
      | _ -> ());
      Tast_iterator.default_iterator.expr iterator e
    in
    let iterator = { Tast_iterator.default_iterator with expr } in
    iterator.expr iterator body;
    all !paths ~f:(fun (env, at, path) ->
        let* path = Source.normalize_value_path env ~at path in
        let* () =
          match path with
          | Path.Pdot _
            when List.exists funcs ~f:(fun target ->
                     (not (List.is_empty target.signature_sites))
                     && List.mem target.paths path ~equal:Path.same) ->
              unsupported at "A pure call through a constrained module signature"
          | _ -> Ok ()
        in
        Ok path)
  in
  let rec close set =
    let* called = all set ~f:(fun f -> references f.body) in
    let called = List.concat called in
    let added =
      List.filter funcs ~f:(fun f ->
          (not (is_in set f))
          && List.exists f.paths ~f:(fun path -> List.mem called path ~equal:Path.same))
    in
    if List.is_empty added then Ok set else close (set @ added)
  in
  close seeds

(** How a predicate is defined: by a body; as a direct invariant; as an invariant in terms
    of its state's fields; or as a view of an invariant's state. *)
type definition =
  | Body of S.term
  | Direct_invariant of S.term
  | Invariant of {
      state : string;
      fields : S.state_field list;
      field_types : Types.type_expr list;
      parameter_types : Types.type_expr list;
      body : S.term;
      field_environment : Env.t;
      field_scope : Proof_scopes.scope option;
    }
  | View of { value : S.term }

(** [t], if it owns the entries of a field of the state [state] by index, as
    [forall i. g -> own s.cells.(i) v]: the index, the guard, the field and the value. *)
let chain_of ~state (t : S.term) =
  match t.term_desc with
  | Tquant (Tforall, [ (i, _) ], body) ->
      begin match spine (S.chain body) [] with
      | { term_desc = Tvar (Qid { pid_str = "->"; _ }); _ }, [ guard; owned ] ->
          begin match spine owned [] with
          | { term_desc = Tvar (Qid { pid_str = "own"; _ }); _ }, [ location; value ] ->
              begin match spine location [] with
              | ( { term_desc = Tvar (Qid { pid_str = "([])"; _ }); _ },
                  [
                    {
                      term_desc =
                        Tfield
                          ( { term_desc = Tvar (Qid { pid_str = s; _ }); _ },
                            Qid { pid_str = field; _ } );
                      _;
                    };
                    { term_desc = Tvar (Qid { pid_str = j; _ }); _ };
                  ] )
                when String.equal s state && String.equal j i.S.pid_str ->
                  Some (i, guard, field, value)
              | _ -> None
              end
          | _ -> None
          end
      | _ -> None
      end
  | _ -> None

(** The fields of the state [state] that [t] mentions, as [s.f]. *)
let rec state_fields ~state (t : S.term) =
  match t.term_desc with
  | Tfield ({ term_desc = Tvar (Qid { pid_str = s; _ }); _ }, Qid { pid_str = f; _ })
    when String.equal s state ->
      [ f ]
  | _ -> List.concat_map (subterms t) ~f:(state_fields ~state)

let rec mentions_own (t : S.term) =
  match t.term_desc with
  | Tvar (Qid { pid_str = "own"; _ }) -> true
  | _ -> List.exists (subterms t) ~f:mentions_own

(** The parts of [st]'s invariant, whose body is [body]: its conjuncts that own resources
    by quantifying, and the registrations of its pending fields. Only an invariant with a
    history has them, as its steps say how the existentials that the parts mention change.
*)
let invariant_parts types (st : structure) body =
  if not (has_history st) then []
  else
    let existential field = st.state ^ "_" ^ field in
    (* In the order of the invariant's existentials. *)
    let ordered uses =
      List.filter
        (List.map st.fields ~f:(fun (_, raven, _, _, _) -> raven)
        @ List.map st.pendings ~f:(fun p -> p.pending_on)
        @ List.map st.chains ~f:snd)
        ~f:(List.mem uses ~equal:String.equal)
    in
    let contents field =
      match List.find st.fields ~f:(fun (f, _, _, _, _) -> String.equal f field) with
      | Some (_, _, _, t, _) -> (
          match Datatypes.desc types t with
          | Tconstr (_, [ atomic ], _) -> (
              match Datatypes.desc types atomic with
              | Tconstr (_, [ contents ], _) -> Atomics contents
              | _ -> Unknown)
          | _ -> Unknown)
      | None -> Unknown
    in
    let conjunct_parts =
      List.filter_mapi (conjuncts body) ~f:(fun n t ->
          let mentioned = List.map (state_fields ~state:st.state t) ~f:existential in
          match (chain_of ~state:st.state t, t.term_desc) with
          | Some (_, _, field, _), _
            when List.Assoc.mem st.chains field ~equal:String.equal ->
              Some
                {
                  part_pred = member_name st ("owns_" ^ field);
                  part_source = `Conjunct n;
                  part_uses =
                    ordered
                      (List.Assoc.find_exn st.chains field ~equal:String.equal
                      :: existential field :: mentioned);
                  part_owns = contents field;
                }
          | _, Tquant (Tforall, _, _) when mentions_own t ->
              Some
                {
                  part_pred = member_name st ("part_" ^ Int.to_string n);
                  part_source = `Conjunct n;
                  part_uses = ordered mentioned;
                  part_owns = Unknown;
                }
          | _ -> None)
    in
    let pending_parts =
      List.map st.pendings ~f:(fun p ->
          let helping_state, helping_key, _ = p.helping in
          {
            part_pred = pending_name st p "registrations";
            part_source = `Pending p.pending_field;
            part_uses =
              ordered
                (existential p.pending_field :: p.pending_on
                 :: List.concat_map st.chains ~f:(fun (field, index) ->
                     [ index; existential field ])
                @ List.map (state_fields ~state:helping_state helping_key) ~f:existential
                );
            part_owns = Ghost;
          })
    in
    conjunct_parts @ pending_parts

(** The members generated for the state of [st]: the state of its growing fields as a data
    type and its order, with transitivity; and, if it has a history, the history as a
    resource algebra in the encoding [history], with what defines it, its ghost field, and
    lemmas taking snapshots of the history and growing it. *)
let structure_members ~(history : History.encoding) types (st : structure) ~at :
    (R.Member.t list, error) Result.t =
  let l = loc at in
  let n x = R.Name.make ~loc:l x in
  let qn m x = generated_module_member ~loc:l m x in
  let var x = R.Expr.var ~loc:l (n x) in
  let call f args = R.Expr.call ~loc:l f args in
  let bin op a b = R.Expr.binary ~loc:l op a b in
  let state_module = module_name st "state" in
  let state_type = R.Type.named ~loc:l (qn state_module "T") [] in
  let decl x t = R.Var.make ~loc:l (ident ~loc:l x) t in
  let length s = call (qn "Seq" "length") [ s ] in
  let extends a b = call (qualified_name ~loc:l (member_name st "extends")) [ a; b ] in
  let order_module = module_name st "order"
  and set_module = module_name st "states"
  and history_module = module_name st "history" in
  let elements = history_elements ~loc:l history st in
  let history_field = member_name st "history" in
  let* structure_typ = Datatypes.typ types ~at st.structure_type in
  let* anchored =
    match anchor_location types st.structure_type with
    | Some at ->
        Ok
          (fun e ->
            R.Expr.field ~loc:l (at ~loc:l e) (qualified_name ~loc:l history_field))
    | None ->
        error at "The structure of a state is a reference: an atomic, a ref or a record"
  in
  let state_data =
    R.Member.module_ ~loc:l
      (generated_ident ~loc:l state_module)
      [
        R.Member.type_ ~loc:l (ident ~loc:l "T")
          (Some
             (R.Type.data ~loc:l
                [
                  R.Type.variant ~loc:l (ident ~loc:l "state")
                    (List.filter_map st.fields ~f:(fun (f, _, typ, _, grows) ->
                         Option.some_if grows (ident ~loc:l f, typ)));
                ]));
      ]
  in
  (* Sequences grow by prefix, pending calls by inclusion, integers by <=. *)
  let order =
    let a = var "a" and b = var "b" in
    let field e f = R.Expr.field ~loc:l e (n f) in
    let grows =
      List.filter_map st.fields ~f:(fun (f, _, _, t, grows) ->
          if not grows then None
          else
            match Datatypes.desc types t with
            | Tconstr (p, [ _ ], _)
              when Option.exists (Datatypes.find types p) ~f:Datatypes.is_sequence ->
                Some
                  (bin And
                     (bin Leq (length (field a f)) (length (field b f)))
                     (bin Eq (field a f)
                        (R.Expr.slice_to ~loc:l (field b f) (length (field a f)))))
            | _ when List.exists st.pendings ~f:(fun p -> String.equal p.pending_field f)
              ->
                Some (bin Subseteq (field a f) (field b f))
            | _ -> Some (bin Leq (field a f) (field b f)))
    in
    Option.value (List.reduce grows ~f:(bin And)) ~default:(R.Expr.bool ~loc:l true)
  in
  (* For the monotone encoding: sequences are compatible if one is a prefix of the other,
     and join to the longer one; pending calls join to their union, integers to their
     maximum. *)
  let compat, join =
    let a = var "a" and b = var "b" in
    let field e f = R.Expr.field ~loc:l e (n f) in
    let parts =
      List.filter_map st.fields ~f:(fun (f, _, _, t, grows) ->
          if not grows then None
          else
            let x = field a f and y = field b f in
            match Datatypes.desc types t with
            | Tconstr (p, [ _ ], _)
              when Option.exists (Datatypes.find types p) ~f:Datatypes.is_sequence ->
                let shorter = bin Leq (length x) (length y) in
                Some
                  ( Some
                      (R.Expr.ite ~loc:l shorter
                         (bin Eq x (R.Expr.slice_to ~loc:l y (length x)))
                         (bin Eq y (R.Expr.slice_to ~loc:l x (length y)))),
                    R.Expr.ite ~loc:l shorter y x )
            | _ when List.exists st.pendings ~f:(fun p -> String.equal p.pending_field f)
              ->
                Some (None, bin Union x y)
            | _ -> Some (None, R.Expr.ite ~loc:l (bin Leq x y) y x))
    in
    ( Option.value
        (List.reduce (List.filter_map parts ~f:fst) ~f:(bin And))
        ~default:(R.Expr.bool ~loc:l true),
      call (qn state_module "state") (List.map parts ~f:snd) )
  in
  let func name formals ret body =
    R.Member.callable
      (R.Callable.func ~loc:l ~formals
         ~returns:[ decl "ret" ret ]
         (generated_ident ~loc:l name) (Some body))
  in
  let lemma ?auto ?triggers name formals ~requires ~ensures body =
    R.Member.callable
      (R.Callable.proc ~loc:l ~kind:Lemma ?auto ~formals
         ~requires:(List.map requires ~f:R.Spec.make)
         ~ensures:(List.map ensures ~f:(R.Spec.make ?triggers))
         (generated_ident ~loc:l name) (Some body))
  in
  let fpu location a b = R.Stmt.call ~loc:l (call (n "fpu") [ location; a; b ]) in
  let order_function name ret body =
    R.Member.callable
      (R.Callable.func ~loc:l
         ~formals:
           [
             decl "a" (R.Type.named ~loc:l (n "T") []);
             decl "b" (R.Type.named ~loc:l (n "T") []);
           ]
         ~returns:[ decl "ret" ret ]
         (ident ~loc:l name) (Some body))
  in
  let instance name ~def =
    R.Member.instance ~loc:l ~def:(name, def) (generated_ident ~loc:l history_module) name
  in
  (* The history's resource algebra, and what defines it. *)
  let algebra =
    match history with
    | Sets ->
        let library = R.Name.make ~loc:l ~path:[ "Library" ] in
        [
          func (member_name st "states")
            [ decl "s" state_type ]
            (R.Type.set ~loc:l state_type)
            (R.Expr.set_compr ~loc:l (decl "e" state_type) (extends (var "e") (var "s")));
          R.Member.instance ~loc:l
            ~def:(library "SetRA", [ state_type ])
            (generated_ident ~loc:l set_module)
            (library "SetRA");
          instance (library "Auth")
            ~def:[ R.Type.named ~loc:l (qualified_name ~loc:l set_module) [] ];
        ]
    | Monotone ->
        [
          R.Member.module_ ~loc:l
            ~implements:[ (n Monotone_history.order_interface, []) ]
            (generated_ident ~loc:l order_module)
            ([
               R.Member.type_ ~loc:l ~rep:true (ident ~loc:l "T") (Some state_type);
               order_function "le" (R.Type.bool ~loc:l) (extends (var "a") (var "b"));
               order_function "compat" (R.Type.bool ~loc:l) compat;
               order_function "join" (R.Type.named ~loc:l (n "T") []) join;
             ]
            @ Monotone_history.laws R.Callable.Lemma);
          instance (n Monotone_history.algebra)
            ~def:[ R.Type.named ~loc:l (qualified_name ~loc:l order_module) [] ];
        ]
  in
  let x = var "x" and s = var "s" and s1 = var "s1" and s2 = var "s2" in
  let history = anchored x in
  Ok
    ([
       state_data;
       func (member_name st "extends")
         [ decl "a" state_type; decl "b" state_type ]
         (R.Type.bool ~loc:l) order;
       (* Triggered by two steps of the order, as Z3 would choose, but fixed. *)
       lemma ~auto:true
         ~triggers:[ [ extends (var "a") (var "b"); extends (var "b") (var "c") ] ]
         (member_name st "extends_trans")
         [ decl "a" state_type; decl "b" state_type; decl "c" state_type ]
         ~requires:[ bin And (extends (var "a") (var "b")) (extends (var "b") (var "c")) ]
         ~ensures:[ extends (var "a") (var "c") ]
         [];
     ]
    @ (if not (has_history st) then []
       else
         algebra
         @ [
             R.Member.field ~loc:l ~ghost:true
               (generated_ident ~loc:l history_field)
               (R.Type.named ~loc:l (qualified_name ~loc:l history_module) []);
             (* Takes note of the current state. *)
             lemma (member_name st "snapshot")
               [ decl "x" structure_typ; decl "s" state_type ]
               ~requires:[ R.Expr.own ~loc:l [ history; elements.auth s ] ]
               ~ensures:[ R.Expr.own ~loc:l [ history; elements.auth_frag s s ] ]
               [ fpu history (elements.auth s) (elements.auth_frag s s) ];
             (* Moves the history on to a state that extends the current one. *)
             lemma (member_name st "learn")
               [ decl "x" structure_typ; decl "s1" state_type; decl "s2" state_type ]
               ~requires:
                 [
                   bin And
                     (R.Expr.own ~loc:l [ history; elements.auth s1 ])
                     (extends s1 s2);
                 ]
               ~ensures:[ R.Expr.own ~loc:l [ history; elements.full s2 ] ]
               [ fpu history (elements.auth s1) (elements.full s2) ];
             (* A snapshot precedes the current state. *)
             (let t = var "t" in
              let both = R.Expr.own ~loc:l [ history; elements.auth_frag t s ] in
              lemma (member_name st "observe")
                [ decl "x" structure_typ; decl "s" state_type; decl "t" state_type ]
                ~requires:[ both ]
                ~ensures:[ both; extends s t ]
                []);
           ])
    @ List.map st.chains ~f:(fun (field, _) ->
        (* A later state keeps the entries of an earlier one at their positions. *)
        let t = var "t" and k = var "k" in
        let entries e = R.Expr.field ~loc:l e (n field) in
        let within e =
          bin And (bin Leq (R.Expr.int ~loc:l 0) k) (bin Lt k (length (entries e)))
        in
        lemma
          (member_name st ("kept_" ^ field))
          [ decl "s" state_type; decl "t" state_type; decl "k" (R.Type.int ~loc:l) ]
          ~requires:[ bin And (extends s t) (within s) ]
          ~ensures:
            [
              bin And (within t)
                (bin Eq
                   (R.Expr.index ~loc:l (entries t) k)
                   (R.Expr.index ~loc:l (entries s) k));
            ]
          []))

(** The views that bind the implicit parameters of the function [f] in its atomic
    precondition, as [queue q xs]: the parameter, the view and its ghost field. *)
let view_bindings env (f : func) =
  let atomic_requires =
    Option.value_map f.contract ~default:[] ~f:(fun c -> c.atomic_requires)
  in
  List.filter_map (List.concat_map atomic_requires ~f:conjuncts) ~f:(fun t ->
      match spine t [] with
      | { term_desc = Tvar q; _ }, args ->
          let key = logical_key env q in
          let v = key in
          begin match
            ( List.Assoc.find env.ctx.given.shared.views v ~equal:String.equal,
              List.last args )
          with
          | Some field, Some { term_desc = Tvar (Qid { pid_str = x; _ }); _ } ->
              Some (x, v, field)
          | _ -> None
          end
      | _ -> None)

(** [t] without the applications of predicates in its conjunctions. *)
let rec without_predicates env (t : S.term) : S.term =
  match spine (S.chain t) [] with
  | ({ term_desc = Tvar (Qid { pid_str = "&&" | "/\\"; _ }); _ } as op), [ a; b ] ->
      let a = without_predicates env a and b = without_predicates env b in
      S.mk_term (Tapply (S.mk_term (Tapply (op, a)) t.term_loc, b)) t.term_loc
  | { term_desc = Tvar q; _ }, _
    when List.Assoc.mem env.ctx.given.preds (logical_key env q) ~equal:String.equal
         || String.equal (qualid_key q) "own" ->
      S.mk_term Ttrue t.term_loc
  | _ -> t

(** The members of the pending field [p] of [st], whose calls of [helped], the procedure
    [helped_proc], wait: the ghost fields of a registration, the predicate holding its
    call's update until the call retires, committed with the result once helped, and the
    lemma helping the registrations waiting on a key. *)
let pending_members ctx (st : structure) (p : pending) (helped : func) ~helped_proc
    ~helped_declaration =
  let at = st.at in
  let l = loc at in
  let n x = R.Name.make ~loc:l x in
  let var x = R.Expr.var ~loc:l (n x) in
  let bin op a b = R.Expr.binary ~loc:l op a b in
  let field e f = R.Expr.field ~loc:l e (qualified_name ~loc:l (pending_name st p f)) in
  let half e f v = R.Expr.own ~loc:l [ field e f; v; R.Expr.real ~loc:l 0.5 ] in
  let decl ?(ghost = false) x t = R.Var.make ~loc:l ~ghost (ident ~loc:l x) t in
  let open State.Syntax in
  let* key_typ = State.typ ctx ~at p.key_type in
  let bool_typ = R.Type.bool ~loc:l and ref_typ = R.Type.ref ~loc:l in
  let* params =
    State.all st.params ~f:(fun (x, t) ->
        let+ typ = State.typ ctx ~at t in
        (x, t, decl x typ))
  in
  let args = List.map params ~f:(fun (x, _, _) -> var x) in
  let* result_name, arg_names =
    State.of_result
      (contract_names helped
         (Option.bind helped.contract ~f:(fun c -> c.header))
         (List.length helped.params))
  in
  let env =
    {
      ctx;
      var_types = List.map params ~f:(fun (x, t, _) -> (x, t));
      logical_definition = false;
      data = ctx.given.types;
      funcs = ctx.given.spec_funcs;
      vars = List.map params ~f:(fun (x, _, _) -> (x, Raven x));
    }
  in
  (* The arguments of the helped calls' updates, by the helped function's parameters, as
     the structure's: those parameters themselves, or for a function taking the
     structure as a ghost parameter, its field that a precondition makes a parameter,
     and a copy's witness, its constructor. *)
  let same_parameters = List.length helped.params = List.length params in
  let* helped_args =
    if same_parameters then
      State.return
        (List.map2_exn arg_names params ~f:(fun name (x, t, _) -> (name, var x, t)))
    else
      let structure = match params with [ (x, _, _) ] -> Some x | _ -> None in
      let ghosts = List.map (ghost_params helped) ~f:(fun (id, _) -> id.S.pid_str) in
      let requires =
        Option.value_map helped.contract ~default:[] ~f:(fun c -> c.requires)
      in
      let field_of name =
        List.find_map requires ~f:(fun t ->
            match spine (S.chain t) [] with
            | ( { term_desc = Tvar (Qid { pid_str = "=="; _ }); _ },
                [
                  { term_desc = Tvar (Qid { pid_str = x; _ }); _ };
                  ({ term_desc = Tfield ({ term_desc = Tvar (Qid g); _ }, _); _ } as field);
                ] )
              when String.equal x name && List.mem ghosts g.pid_str ~equal:String.equal ->
                Some (g.pid_str, field)
            | _ -> None)
      in
      let* regular =
        State.all (List.zip_exn arg_names helped.params) ~f:(fun (name, param) ->
            let pattern_type =
              match param.Typedtree.fp_kind with
              | Tparam_pat p | Tparam_optional_default (p, _) -> Some p.pat_type
            in
            match (name, pattern_type, helped.copy_for, structure) with
            | Some name, Some t, Some copy, _
              when String.equal name (Ident.name copy.witness) ->
                begin match Witnesses.witness_type ctx.given.types t with
                | Some (data, _, _) ->
                    let c =
                      List.find_exn data.ctors ~f:(fun c ->
                          String.equal c.Datatypes.ocaml copy.constructor)
                    in
                    State.return
                      ( Some name,
                        R.Expr.call ~loc:l (Datatypes.ctor_name ~loc:l data c) [],
                        Witnesses.substitute_newtypes copy.newtypes t )
                | None -> State.of_result (error at "A copy's witness of no witness type")
                end
            | Some name, Some _, _, Some structure ->
                begin match field_of name with
                | Some (ghost, field) ->
                    let env = bind env ghost (Raven structure) in
                    let env =
                      {
                        env with
                        var_types = (ghost, List.hd_exn st.params |> snd) :: env.var_types;
                      }
                    in
                    let* value = formula env field in
                    let+ t =
                      State.of_result
                        (Report.expect ~at "The type of a helped call's argument"
                           (term_type env field))
                    in
                    (Some name, value, t)
                | None ->
                    State.of_result
                      (unsupported helped.loc
                         "Helping a function with a parameter that is neither the \
                          structure nor its field")
                end
            | _ ->
                State.of_result
                  (unsupported helped.loc
                     "Helping a function whose parameters are not those of the \
                      structure's invariant"))
      in
      let ghost =
        List.map ghosts ~f:(fun name ->
            (Some name, var (Option.value_exn structure), List.hd_exn st.params |> snd))
      in
      State.return (regular @ ghost)
  in
  (* The update's arguments, and the results it commits with: the result, and for a
     function that may raise, no exception. *)
  let tuple = function [ e ] -> e | es -> R.Expr.tuple ~loc:l es in
  let au_args = [ tuple (List.map helped_args ~f:(fun (_, value, _) -> value)) ] in
  let* outcome_typ = State.typ ctx ~at outcome_type in
  let returned v =
    if Option.exists helped.contract ~f:raising_contract then
      tuple [ v; no_exception ~loc:l outcome_typ ]
    else v
  in
  let _, _, helped_result = p.helping in
  (* A result that depends on the key's contents after the helping action is stored in
     the registration, as the invariant relates it to them. *)
  let carried = Option.is_some helped_result.contents in
  let* contents_typ =
    let* contents = State.of_result (key_contents ctx.given.types ~at p.key_type) in
    State.typ ctx ~at contents
  in
  let* result, result_type =
    helped_value env ~at ~key_type:p.key_type helped_result (var "contents")
  in
  let* result_typ = State.typ ctx ~at result_type in
  let* helped_proc =
    if same_parameters then
      let occurrence =
        List.fold_right st.params ~init:result_type ~f:(fun (_, argument) result ->
            Btype.newgenty
              (Tarrow
                 (Nolabel, Btype.newgenty (Tpoly (argument, [])), result, Types.commu_ok)))
      in
      State.polymorphic_call ctx ~at ~path:(List.hd_exn helped.paths)
        ~declaration:helped_declaration ~occurrence ~target:helped_proc
    else
      (* Its instance at the structure's type arguments, which its variables are. *)
      match
        ( Path_bindings.find ctx.given.polymorphic_functions (List.hd_exn helped.paths),
          Datatypes.desc ctx.given.types (List.hd_exn st.params |> snd) )
      with
      | None, _ -> State.return helped_proc
      | Some worker, Tconstr (_, arguments, _)
        when List.length arguments = List.length worker.scheme.variables ->
          let+ instance = State.value_instance ctx ~at ~target:worker.name ~arguments in
          instance ^ "." ^ (Qualified_name.of_string helped_proc).name
      | Some _, _ ->
          State.of_result
            (unsupported helped.loc
               "Helping a generic function whose type parameters are not the structure's")
  in
  let token_typ = R.Type.atomic_token ~loc:l (qualified_name ~loc:l helped_proc) in
  let registration = pending_name st p "registration" in
  let registered hc =
    R.Expr.call ~loc:l (qualified_name ~loc:l registration) (hc :: args)
  in
  let fields =
    [
      ("watched", key_typ);
      ("linked", bool_typ);
      ("token", token_typ);
      ("retired", bool_typ);
    ]
    @ if carried then [ ("result", result_typ) ] else []
  in
  let ghost_fields =
    List.map fields ~f:(fun (f, t) ->
        R.Member.field ~loc:l ~ghost:true (generated_ident ~loc:l (pending_name st p f)) t)
  in
  (* The registration of a call: its update until it retires, committed once helped. *)
  let hc = var "hc" in
  (* A carried result: all of it until linked, half of it after, with the invariant's
     half relating it to the key's contents. *)
  let committed, stored =
    if carried then
      ( var "res",
        [
          R.Expr.ite ~loc:l (var "l")
            (half hc "result" (var "res"))
            (R.Expr.own ~loc:l [ field hc "result"; var "res"; R.Expr.real ~loc:l 1.0 ]);
        ] )
    else (result, [])
  in
  let registration_pred =
    R.Callable.func ~loc:l ~kind:Pred
      ~formals:(decl "hc" ref_typ :: List.map params ~f:(fun (_, _, d) -> d))
      (generated_ident ~loc:l registration)
      (Some
         (R.Expr.exists ~loc:l
            ([ decl "tok" token_typ; decl "l" bool_typ; decl "r" bool_typ ]
            @ if carried then [ decl "res" result_typ ] else [])
            (List.reduce_exn ~f:(bin And)
               ([
                  half hc "token" (var "tok");
                  half hc "linked" (var "l");
                  half hc "retired" (var "r");
                ]
               @ stored
               @ [
                   R.Expr.ite ~loc:l (var "r") (R.Expr.bool ~loc:l true)
                     (R.Expr.ite ~loc:l (var "l")
                        (R.Expr.au_commit ~loc:l
                           (qualified_name ~loc:l helped_proc)
                           ((var "tok" :: au_args) @ [ returned committed ]))
                        (R.Expr.au ~loc:l
                           (qualified_name ~loc:l helped_proc)
                           (var "tok" :: au_args)));
                 ]))))
  in
  (* The values of the structure's views, which the helped function's implicit
     parameters are bound to by its atomic precondition. *)
  let* scope_env = scope_env ctx in
  let bindings = view_bindings scope_env helped in
  let* () =
    if List.length bindings <= 1 then State.return ()
    else
      State.of_result
        (unsupported helped.loc "Helping a function with several implicit parameters")
  in
  let* view_values =
    State.all st.views ~f:(fun ((v : S.predicate), _) ->
        let v = v.pred_name.pid_str in
        let* t =
          match List.Assoc.find ctx.given.preds v ~equal:String.equal with
          | Some (_, types) when not (List.is_empty types) ->
              State.return (List.last_exn types)
          | _ -> State.of_result (error at (Printf.sprintf "The view %s has no value" v))
        in
        let+ typ = State.typ ctx ~at t in
        let view_field = view_field_in ctx.given.shared v in
        ("view_" ^ v, v, view_field, t, typ))
  in
  let anchored e =
    match anchor_location ctx.given.types st.structure_type with
    | Some at -> at ~loc:l e
    | None -> e
  in
  let structure = List.hd_exn args in
  let view_owned =
    List.map view_values ~f:(fun (x, _, view_field, _, _) ->
        View_storage.own ~loc:l ~field:view_field (anchored structure) (var x) 0.5)
  in
  (* The helped function's atomic postcondition, for the result, without its predicates. *)
  let post_env =
    List.fold view_values
      ~init:
        (List.fold helped_args ~init:env ~f:(fun env (name, value, t) ->
             match name with
             | Some name ->
                 {
                   (bind env name (Value value)) with
                   var_types = (name, t) :: env.var_types;
                 }
             | None -> env))
      ~f:(fun env (x, v, _, t, _) ->
        match List.find bindings ~f:(fun (_, w, _) -> String.equal v w) with
        | Some (implicit, _, _) ->
            {
              (bind env implicit (Raven x)) with
              var_types = (implicit, t) :: env.var_types;
            }
        | None -> env)
  in
  let post_env =
    {
      (bind post_env result_name (Value result)) with
      var_types = (result_name, result_type) :: post_env.var_types;
    }
  in
  let+ posts =
    State.all
      (Option.value_map helped.contract ~default:[] ~f:(fun c -> c.atomic_ensures))
      ~f:(fun t -> formula post_env (without_predicates scope_env t))
  in
  let c = var "c" and regs = var "regs" and on = var "on" and ls = var "ls" in
  let each body =
    R.Expr.forall ~loc:l [ decl "hc" ref_typ ] (bin Impl (bin In hc regs) body)
  in
  let waits_on_c = bin Eq (R.Expr.index ~loc:l on hc) c in
  let help = pending_name st p "help" in
  let call f es = R.Stmt.call ~loc:l (R.Expr.call ~loc:l (qualified_name ~loc:l f) es) in
  let local ?init x t = R.Stmt.local ~loc:l ~ghost:true ?init ~typ:t (ident ~loc:l x) in
  (* Opening a helped call's update, with the values of its implicit parameters, and
     committing it with the result. *)
  let bound =
    List.filter view_values ~f:(fun (_, v, _, _, _) ->
        List.exists bindings ~f:(fun (_, w, _) -> String.equal v w))
  in
  let opened_values = List.map bound ~f:(fun (x, _, _, _, _) -> var (x ^ "_1")) in
  let view_uses use =
    List.map bound ~f:(fun (x, v, _, _, _) ->
        let raven, _ = List.Assoc.find_exn ctx.given.preds v ~equal:String.equal in
        use ~loc:l (qualified_name ~loc:l raven) (args @ [ var (x ^ "_1") ]))
  in
  let commit =
    List.concat_map bound ~f:(fun (x, _, _, _, typ) -> local (x ^ "_1") typ)
    @ [
        (match opened_values with
        | [] -> call "openAU" (var "tok" :: au_args)
        | _ ->
            R.Stmt.assign ~loc:l opened_values
              (R.Stmt.expr_rhs (R.Expr.call ~loc:l (n "openAU") (var "tok" :: au_args))));
      ]
    @ view_uses (fun ~loc p args -> R.Stmt.unfold ~loc p args)
    @ view_uses (fun ~loc p args -> R.Stmt.fold ~loc p args)
    @ [ call "commitAU" ((var "tok" :: au_args) @ [ returned result ]) ]
  in
  let body =
    [
      R.Stmt.if_ ~loc:l
        (bin Neq regs (R.Expr.set ~loc:l []))
        (local "hc" ref_typ
           ~init:(R.Stmt.expr_rhs (R.Expr.call ~loc:l (n "choose") [ regs ]))
        @ [
            call help
              (args @ [ c ]
              @ (if carried then [ var "contents" ] else [])
              @ List.map view_values ~f:(fun (x, _, _, _, _) -> var x)
              @ [ R.Expr.call ~loc:l (n "--") [ regs; R.Expr.set ~loc:l [ hc ] ]; on; ls ]
              );
            R.Stmt.if_ ~loc:l waits_on_c
              (local "tok" token_typ @ local "r" bool_typ
              @ [
                  R.Stmt.unfold ~loc:l
                    ~witnesses:
                      [ (ident ~loc:l "tok", var "tok"); (ident ~loc:l "r", var "r") ]
                    (qualified_name ~loc:l registration)
                    (hc :: args);
                  R.Stmt.if_ ~loc:l (R.Expr.not_ ~loc:l (var "r")) commit [];
                ]
              @ (if carried then
                   [ R.Stmt.assign ~loc:l [ field hc "result" ] (R.Stmt.expr_rhs result) ]
                 else [])
              @ [
                  R.Stmt.assign ~loc:l
                    [ field hc "linked" ]
                    (R.Stmt.expr_rhs (R.Expr.bool ~loc:l true));
                  R.Stmt.fold ~loc:l
                    ~witnesses:
                      ([
                         (ident ~loc:l "tok", var "tok");
                         (ident ~loc:l "l", R.Expr.bool ~loc:l true);
                         (ident ~loc:l "r", var "r");
                       ]
                      @ if carried then [ (ident ~loc:l "res", result) ] else [])
                    (qualified_name ~loc:l registration)
                    (hc :: args);
                ])
              [];
          ])
        [];
    ]
  in
  let help_lemma =
    R.Callable.proc ~loc:l ~kind:Lemma
      ~formals:
        (List.map params ~f:(fun (_, _, d) -> d)
        @ [ decl "c" key_typ ]
        @ (if carried then [ decl "contents" contents_typ ] else [])
        @ List.map view_values ~f:(fun (x, _, _, _, typ) -> decl x typ)
        @ [
            decl "regs" (R.Type.fin_set ~loc:l ref_typ);
            decl "on" (R.Type.map ~loc:l ref_typ key_typ);
            decl "ls" (R.Type.map ~loc:l ref_typ bool_typ);
          ])
      ~requires:
        (List.map view_owned ~f:R.Spec.make
        @ [
            (* The helped calls' atomic postconditions hold if some call waits on [c]. *)
            R.Spec.make
              (each
                 (List.reduce_exn ~f:(bin And)
                    ([
                       half hc "linked" (R.Expr.index ~loc:l ls hc);
                       registered hc;
                       bin Impl waits_on_c
                         (R.Expr.not_ ~loc:l (R.Expr.index ~loc:l ls hc));
                     ]
                    @ List.map posts ~f:(bin Impl waits_on_c))));
          ])
      ~ensures:
        (List.map view_owned ~f:R.Spec.make
        @ [
            R.Spec.make
              (each
                 (List.reduce_exn ~f:(bin And)
                    ([
                       half hc "linked" (bin Or (R.Expr.index ~loc:l ls hc) waits_on_c);
                       registered hc;
                     ]
                    @
                    if carried then
                      [
                        R.Expr.ite ~loc:l waits_on_c (half hc "result" result)
                          (R.Expr.bool ~loc:l true);
                      ]
                    else [])));
          ])
      ~decreases:[ regs ] (generated_ident ~loc:l help) (Some body)
  in
  ghost_fields @ [ R.Member.callable registration_pred; R.Member.callable help_lemma ]

(** The parameters of [p], with the OCaml types [param_types], and the environment of the
    predicate's body. *)
let pred_params ctx ~at (p : S.predicate) param_types =
  let open State.Syntax in
  let l = loc at in
  let+ params =
    State.all (List.zip_exn p.pred_params param_types) ~f:(fun ((id, _), t) ->
        let* typ = State.typ ctx ~at t in
        let+ raven = State.fresh id.S.pid_str in
        (id.pid_str, raven, t, R.Var.make ~loc:(loc id.pid_loc) (ident ~loc:l raven) typ))
  in
  let env =
    {
      ctx;
      var_types = List.map params ~f:(fun (x, _, t, _) -> (x, t));
      logical_definition = false;
      data = ctx.given.types;
      funcs = ctx.given.spec_funcs;
      vars = List.map params ~f:(fun (x, raven, _, _) -> (x, Raven raven));
    }
  in
  (params, env)

type checked_operation = {
  operation_binding : Module_inventory.checked_binding;
  operation_signature : Module_inventory.signature_value;
  operation_contract : S.contract option;
  operation_name : string;
  operation_member : string;
  operation_paths : Path.t list;
}

type resource_signature = {
  resource_paths : Path.t list;
  resource_declaration : S.predicate;
  resource_backend : string;
  resource_types : Types.type_expr list;
  resource_raw_types : Types.type_expr list;
}

type checked_view = {
  view_binding : Module_inventory.checked_binding;
  view_key : string;
  view_resources : (Module_inventory.signature_resource * resource_signature) list;
  view_source_substitution : Subst.t;
  view_actual_substitution : Subst.t;
  view_types : Datatypes.t list;
}

let checked_type_substitution ?(substitution = Subst.identity) binding path =
  let substitution =
    List.fold binding.Module_inventory.expected.signature_ghost_modules ~init:substitution
      ~f:(fun substitution (name, formal) ->
        let resource = formal.Module_inventory.ghost_resource in
        let owner = Subst.module_path substitution (Path.Pdot (path, name)) in
        let substitution = Subst.add_module resource.resource_id owner substitution in
        List.fold resource.resource_type_members ~init:substitution
          ~f:(fun substitution (member, id, _) ->
            Subst.add_type id (Path.Pdot (owner, String.uncapitalize member)) substitution))
  in
  List.fold binding.Module_inventory.expected.signature_types ~init:substitution
    ~f:(fun substitution (name, declaration) ->
      Subst.add_type declaration.Typedtree.typ_id
        (Subst.module_path substitution (Path.Pdot (path, name)))
        substitution)

let checked_raw_types types binding =
  let aliases =
    List.map binding.Module_inventory.expected.signature_ghost_modules
      ~f:(fun (_, formal) ->
        let resource = formal.Module_inventory.ghost_resource in
        {
          resource.resource_descriptor with
          Datatypes.alias =
            Some (Subst.type_expr binding.parameter_substitution resource.resource_type);
        })
  in
  aliases
  @ List.map types ~f:(fun data ->
      let paths =
        List.filter_map binding.Module_inventory.expected.signature_types
          ~f:(fun (name, declaration) ->
            if Datatypes.declares data (Path.Pdot (binding.actual_path, name)) then
              Some (Path.Pident declaration.Typedtree.typ_id)
            else None)
      in
      Datatypes.with_paths data paths)

let signature_contract (signature : Module_inventory.signature_value) =
  let site = signature.site in
  contract_after ~scope:site.scope site.annotations ~item_loc:site.item_loc
    ~next:site.next

type prepared_callable = {
  prepared_formals : R.Var.t list;
  prepared_args : R.Expr.t list;
  prepared_implicit : (string * string * Types.type_expr * R.Type.t * R.Loc.t) list;
  prepared_roles : (bool * bool) list;
  prepared_returns : R.Var.t list;
  prepared_requires : R.Spec.t list;
  prepared_ensures : R.Spec.t list;
  prepared_logical_ensures : R.Spec.t list;
}
(** The contract declaration shared by imports and checked forwarding procedures. *)

let prepare_callable ?(validate = false) ?raising ctx ~(at : Location.t) ~args ~result
    (contract : S.contract option) =
  let l = loc at in
  let header = Option.bind contract ~f:(fun c -> c.header) in
  let header_names =
    match header with
    | None -> Ok ("result", List.map args ~f:(fun _ -> None))
    | Some h ->
        let* result =
          match h.hd_ret with
          | [ Lvar id ] -> Ok id.pid_str
          | [ Lwild ] | [] -> Ok "result"
          | _ -> unsupported h.hd_name.pid_loc "A contract naming several results"
        in
        let* names =
          all h.hd_args ~f:(function
            | S.Lvar id -> Ok (Some id.pid_str)
            | Lunit _ | Lwild -> Ok None
            | Lghost (id, _) ->
                unsupported id.pid_loc "A ghost parameter of a library's function")
        in
        if List.length names = List.length args then Ok (result, names)
        else
          error h.hd_name.pid_loc
            (Printf.sprintf "This contract names %d arguments, but this function has %d"
               (List.length names) (List.length args))
  in
  let open State.Syntax in
  let* () =
    State.modify (fun (s : State.state) ->
        { s with names = { s.names with used = Set.add s.names.used "r" } })
  in
  let* result_typ = State.typ ctx ~at result in
  let* () = State.note_domain ctx.given.types result in
  let* result_name, names = State.of_result header_names in
  let* params =
    State.all (List.zip_exn names args) ~f:(fun (n, t) ->
        let* raven = State.fresh (Option.value n ~default:"x") in
        let* typ = State.typ ctx ~at t in
        let+ () = State.note_domain ctx.given.types t in
        (n, raven, t, R.Var.make ~loc:l (ident ~loc:l raven) typ))
  in
  (* A function that may raise, as [raising] says, returns its outcome last. *)
  let* outcome =
    match raising with
    | None -> State.return None
    | Some set ->
        let* typ = State.typ ctx ~at outcome_type in
        let+ raised = State.fresh "raised" in
        Some (set, raised, typ)
  in
  let returns =
    (if is_unit result then [] else [ R.Var.make ~loc:l (ident ~loc:l "r") result_typ ])
    @ Option.value_map outcome ~default:[] ~f:(fun (_, raised, typ) ->
        [ R.Var.make ~loc:l (ident ~loc:l raised) typ ])
  in
  let named =
    (result_name, "r", result)
    :: List.filter_map params ~f:(fun (n, raven, t, _) ->
        Option.map n ~f:(fun n -> (n, raven, t)))
  in
  let env =
    {
      ctx;
      var_types = List.map named ~f:(fun (n, _, t) -> (n, t));
      logical_definition = false;
      data = ctx.given.types;
      funcs = ctx.given.spec_funcs;
      vars = List.map named ~f:(fun (n, raven, _) -> (n, Raven raven));
    }
  in
  let env =
    if is_unit result then bind env result_name (Value (unit_value ~loc:l)) else env
  in
  let env =
    Option.value_map outcome ~default:env ~f:(fun (_, raised, _) ->
        {
          (bind env outcome_name (Raven raised)) with
          var_types = (outcome_name, outcome_type) :: env.var_types;
        })
  in
  let raises = Option.value_map contract ~default:[] ~f:(fun c -> c.raises) in
  let atomic_raises =
    Option.value_map contract ~default:[] ~f:(fun c -> c.atomic_raises)
  in
  let on_return terms =
    if Option.is_some outcome then List.map terms ~f:Exceptions.on_return else terms
  in
  let requires = Option.value_map contract ~default:[] ~f:(fun c -> c.requires) in
  let atomic_requires =
    Option.value_map contract ~default:[] ~f:(fun c -> c.atomic_requires)
  in
  let* implicit = free_typed env (requires @ atomic_requires) ~at in
  let roles =
    List.map implicit ~f:(fun (x, _, _, _, _) ->
        ( List.exists requires ~f:(fun term ->
              List.mem (term_names term) x ~equal:String.equal),
          List.exists atomic_requires ~f:(fun term ->
              List.mem (term_names term) x ~equal:String.equal) ))
  in
  let env =
    List.fold implicit ~init:env ~f:(fun env (n, raven, t, _, _) ->
        { (bind env n (Raven raven)) with var_types = (n, t) :: env.var_types })
  in
  let* () =
    State.of_result
    @@
    if not validate then Ok ()
    else
      let predicates q =
        Option.map
          (List.Assoc.find ctx.given.preds (logical_key env q) ~equal:String.equal)
          ~f:snd
      in
      let clauses =
        Option.value_map contract ~default:[] ~f:(fun c ->
            c.requires @ c.ensures @ c.atomic_requires @ c.atomic_ensures)
      in
      Signature_contract.terms ~expected:Predef.type_bool ~logical_types:ctx.given.types
        ~predicates ~environment:ctx.given.env ~variables:env.var_types clauses
  in
  let* logical_requires = State.all requires ~f:(formula env) in
  let clauses ?atomic terms =
    State.all terms ~f:(fun t ->
        State.map (formula env t) ~f:(fun e -> R.Spec.make ?atomic e))
  in
  let requires = List.map logical_requires ~f:R.Spec.make in
  let* atomic_requires = clauses ~atomic:true atomic_requires in
  let* logical_ensures =
    contract_postcondition_formulas env ~at
      (on_return (Option.value_map contract ~default:[] ~f:(fun c -> c.ensures))
      @ Option.value_map outcome ~default:[] ~f:(fun (set, _, _) ->
          Exceptions.raises_postconditions ctx.given.types ~at raises set))
  in
  let+ atomic_ensures =
    contract_postconditions env ~at ~atomic:true
      (on_return (Option.value_map contract ~default:[] ~f:(fun c -> c.atomic_ensures))
      @ Option.value_map outcome ~default:[] ~f:(fun _ ->
          Exceptions.raises_postconditions ~only:false ctx.given.types ~at
            (List.map atomic_raises ~f:(fun (p, t) -> (p, Some t)))
            (State.Raises [])))
  in
  let ensures = List.map logical_ensures ~f:R.Spec.make in
  let input_domains =
    List.filter_map params ~f:(fun (_, raven, typ, _) ->
        Datatypes.admissible ~loc:l ctx.given.types typ
          (R.Expr.var ~loc:l (Translate_context.name ~loc:l raven)))
  in
  let in_range = List.map input_domains ~f:R.Spec.make in
  let prepared_logical_ensures =
    let result_domain =
      Datatypes.admissible ~loc:l ctx.given.types result
        (R.Expr.var ~loc:l (Translate_context.name ~loc:l "r"))
    in
    List.map
      (Option.to_list result_domain @ logical_ensures)
      ~f:(fun post ->
        R.Spec.make
          (List.fold_right (input_domains @ logical_requires) ~init:post
             ~f:(fun pre post -> R.Expr.binary ~loc:l Impl pre post)))
  in
  let result_in_range =
    match outcome with
    | None -> Option.to_list (value_spec ctx ~loc:l result "r")
    | Some (_, raised, typ) ->
        Option.to_list
          (Option.map
             (Datatypes.admissible ~loc:l ctx.given.types result
                (R.Expr.var ~loc:l (name ~loc:l "r")))
             ~f:(fun admissible ->
               R.Spec.make
                 (R.Expr.binary ~loc:l Impl
                    (R.Expr.binary ~loc:l Eq
                       (R.Expr.var ~loc:l (name ~loc:l raised))
                       (no_exception ~loc:l typ))
                    admissible)))
  in
  {
    prepared_formals =
      List.map params ~f:(fun (_, _, _, v) -> v)
      @ List.map implicit ~f:(fun (_, raven, _, typ, _) ->
          R.Var.make ~loc:l ~ghost:true ~implicit:true (ident ~loc:l raven) typ);
    prepared_args =
      List.map params ~f:(fun (_, raven, _, _) -> R.Expr.var ~loc:l (name ~loc:l raven));
    prepared_implicit = implicit;
    prepared_roles = roles;
    prepared_returns = returns;
    prepared_requires = in_range @ requires @ atomic_requires;
    prepared_ensures = result_in_range @ ensures @ atomic_ensures;
    prepared_logical_ensures;
  }

let prepared_member ~at ~name body prepared =
  R.Callable.proc ~loc:(loc at) ~formals:prepared.prepared_formals
    ~returns:prepared.prepared_returns ~requires:prepared.prepared_requires
    ~ensures:prepared.prepared_ensures
    (ident ~loc:(loc at) name)
    body

(** A checked call with direct argument and result forwarding. *)
let forwarding_body ~at ~self ~target ~result ~atomic prepared =
  let open State.Syntax in
  let l = loc at in
  let var x = R.Expr.var ~loc:l (name ~loc:l x) in
  let* opened =
    if not atomic then State.return []
    else
      State.all prepared.prepared_implicit ~f:(fun (_, _, _, typ, _) ->
          let+ x = State.fresh "opened" in
          (R.Stmt.local ~loc:l ~ghost:true ~typ (ident ~loc:l x), var x))
  in
  let implicit_args =
    if atomic then List.map opened ~f:snd
    else List.map prepared.prepared_implicit ~f:(fun (_, x, _, _, _) -> var x)
  in
  let call =
    R.Expr.call ~loc:l
      (qualified_name ~loc:l target)
      (prepared.prepared_args @ implicit_args)
  in
  let call_statement =
    if is_unit result then R.Stmt.call ~loc:l call
    else R.Stmt.assign ~loc:l [ var "r" ] (R.Stmt.expr_rhs call)
  in
  if not atomic then State.return [ call_statement ]
  else
    let+ token = State.fresh "token" in
    let bind =
      R.Stmt.local ~loc:l ~ghost:true
        ~typ:(R.Type.atomic_token ~loc:l (qualified_name ~loc:l self))
        ~init:(R.Stmt.expr_rhs (R.Expr.call ~loc:l (name ~loc:l "bindAU") []))
        (ident ~loc:l token)
    in
    let open_call = R.Expr.call ~loc:l (name ~loc:l "openAU") [ var token ] in
    let opening =
      match opened with
      | [] -> R.Stmt.call ~loc:l open_call
      | _ -> R.Stmt.assign ~loc:l (List.map opened ~f:snd) (R.Stmt.expr_rhs open_call)
    in
    let commit =
      R.Stmt.call ~loc:l
        (R.Expr.call ~loc:l (name ~loc:l "commitAU")
           [ var token; (if is_unit result then unit_value ~loc:l else var "r") ])
    in
    bind @ List.concat_map opened ~f:fst @ [ opening; call_statement; commit ]

let contains_atomic_token types typ =
  let rec contains seen typ =
    match Datatypes.desc types typ with
    | Tconstr (path, args, _) ->
        List.exists args ~f:(contains seen)
        || (not (List.mem seen path ~equal:Path.same))
           && Option.exists (Datatypes.find types path) ~f:(fun data ->
               Option.is_some data.atomic_procedure
               || List.exists data.ctors ~f:(fun constructor ->
                   List.exists constructor.args ~f:(contains (path :: seen))))
    | Ttuple components -> List.exists components ~f:(fun (_, t) -> contains seen t)
    | _ -> false
  in
  contains [] typ

(** The logical counterpart of an explicitly pure imported procedure. *)
let library_pure_name name = name ^ "$pure"

let library_pure_members ctx ~(at : Location.t) ~name ~args ~result
    (contract : S.contract) =
  let open State.Syntax in
  let l = loc at in
  let* () =
    if List.is_empty args then
      State.of_result (unsupported at "A pure contract on a non-function library value")
    else State.return ()
  in
  let* () =
    if
      contract.atomic || raising_contract contract
      || not
           (List.is_empty contract.atomic_requires
           && List.is_empty contract.atomic_ensures)
    then State.of_result (unsupported at "An atomic or raising pure library function")
    else State.return ()
  in
  let* () =
    let env =
      {
        ctx;
        var_types = [];
        logical_definition = false;
        data = ctx.given.types;
        funcs = ctx.given.spec_funcs;
        vars = [];
      }
    in
    let resource_dependent term =
      List.exists (term_references [] term) ~f:(fun q ->
          String.equal (qualid_key q) "own"
          || List.Assoc.mem ctx.given.preds (logical_key env q) ~equal:String.equal
          || Option.is_some (atomic_method env q))
    in
    if List.exists (contract.requires @ contract.ensures) ~f:resource_dependent then
      State.of_result
        (unsupported at "A pure library function whose contract depends on heap resources")
    else State.return ()
  in
  let* prepared = prepare_callable ctx ~at ~args ~result (Some contract) in
  let* () =
    if List.is_empty prepared.prepared_implicit then State.return ()
    else State.of_result (unsupported at "A pure library function with ghost parameters")
  in
  let logical_name = library_pure_name name in
  let* result_type = State.typ ctx ~at result in
  let logical_returns = [ R.Var.make ~loc:l (ident ~loc:l "r") result_type ] in
  let logical =
    R.Callable.func ~loc:l ~formals:prepared.prepared_formals ~returns:logical_returns
      ~ensures:prepared.prepared_logical_ensures (ident ~loc:l logical_name) None
  in
  let equality =
    if is_unit result then []
    else
      [
        R.Spec.make
          (R.Expr.binary ~loc:l Eq
             (R.Expr.var ~loc:l (Translate_context.name ~loc:l "r"))
             (R.Expr.call ~loc:l
                (Translate_context.name ~loc:l logical_name)
                prepared.prepared_args));
      ]
  in
  let procedure =
    prepared_member ~at ~name None
      { prepared with prepared_ensures = prepared.prepared_ensures @ equality }
  in
  State.return [ logical; procedure ]

(** An assumed library value or procedure, using the shared contract preparation. *)
let library_function ?raising ctx ~(at : Location.t) ~name ~args ~result contract =
  match (args, contract) with
  | [], None ->
      let open State.Syntax in
      let* () = State.note_domain ctx.given.types result in
      let+ result_type = State.typ ctx ~at result in
      let l = loc at in
      R.Callable.func ~loc:l
        ~returns:[ R.Var.make ~loc:l (ident ~loc:l "r") result_type ]
        ~ensures:(Option.to_list (value_spec ctx ~loc:l result "r"))
        (ident ~loc:l name) None
  | [], Some _ ->
      State.of_result
        (unsupported at "A contract of a library's value other than a function")
  | _ ->
      State.map
        (prepare_callable ?raising ctx ~at ~args ~result contract)
        ~f:(prepared_member ~at ~name None)
