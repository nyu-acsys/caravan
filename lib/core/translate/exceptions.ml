(** OCaml's exceptions, as the constructors of one Raven data type for [exn]: those the
    program declares, at the top level or in modules, and the predefined ones it may
    raise. *)

open Base
module S = Caravan_spec.Spec_ast

let ( let* ) = Result.( >>= )

type declared = { name : string; args : Types.type_expr list; at : Location.t }

(** The predefined exceptions, without a payload, that programs may raise. *)
let predefined = [ "Not_found"; "Exit" ]

(** Whether [structure] mentions an exception: declares one, or constructs or matches one.
*)
let mentioned (structure : Typedtree.structure) =
  let found = ref false in
  let extension (cstr : Data_types.constructor_description) =
    match cstr.cstr_tag with Cstr_extension _ -> found := true | _ -> ()
  in
  let iterator =
    {
      Tast_iterator.default_iterator with
      structure_item =
        (fun self item ->
          (match item.str_desc with Tstr_exception _ -> found := true | _ -> ());
          Tast_iterator.default_iterator.structure_item self item);
      expr =
        (fun self e ->
          (match e.exp_desc with
          | Texp_construct (_, cstr, _) -> extension cstr
          | _ -> ());
          Tast_iterator.default_iterator.expr self e);
      pat =
        (fun (type k) self (p : k Typedtree.general_pattern) ->
          (match p.pat_desc with
          | Tpat_construct (_, cstr, _, _) -> extension cstr
          | _ -> ());
          Tast_iterator.default_iterator.pat self p);
    }
  in
  iterator.structure iterator structure;
  !found

(** The exceptions that [structure] declares outside functors, in order. *)
let declared (structure : Typedtree.structure) =
  let rec items in_functor (items : Typedtree.structure_item list) =
    Result.all
      (List.map items ~f:(fun (item : Typedtree.structure_item) ->
           match item.str_desc with
           | Tstr_exception { tyexn_constructor = ext; _ } ->
               if in_functor then
                 Report.unsupported item.str_loc "An exception declared in a functor"
               else
                 begin match ext.ext_kind with
                 | Text_decl (_, Cstr_tuple args, None) ->
                     Ok
                       [
                         {
                           name = ext.ext_name.txt;
                           args =
                             List.map args ~f:(fun (ct : Typedtree.core_type) ->
                                 ct.ctyp_type);
                           at = ext.ext_loc;
                         };
                       ]
                 | Text_decl _ ->
                     Report.unsupported ext.ext_loc
                       "An exception with a record or a GADT payload"
                 | Text_rebind _ -> Report.unsupported ext.ext_loc "An exception alias"
                 end
           | Tstr_module { mb_expr; _ } -> module_expr in_functor mb_expr
           | _ -> Ok []))
    |> Result.map ~f:List.concat
  and module_expr in_functor (m : Typedtree.module_expr) =
    match m.mod_desc with
    | Tmod_structure s -> items in_functor s.str_items
    | Tmod_functor (_, body) -> module_expr true body
    | Tmod_constraint (body, _, _, _) -> module_expr in_functor body
    | Tmod_ident _ | Tmod_apply _ | Tmod_apply_unit _ | Tmod_unpack _ -> Ok []
  in
  let* declared = items false structure.str_items in
  match
    List.find_a_dup
      (List.map declared ~f:(fun d -> d.name) @ predefined)
      ~compare:String.compare
  with
  | Some name ->
      let at =
        Option.value_map
          (List.find declared ~f:(fun d -> String.equal d.name name))
          ~default:Location.none
          ~f:(fun d -> d.at)
      in
      Report.unsupported at
        (Printf.sprintf "Two exceptions named %s, or one named as a predefined one" name)
  | None -> Ok declared

(** The data type of [exn], with the exceptions of [structure], if it mentions any. *)
let datatype (structure : Typedtree.structure) =
  if not (mentioned structure) then Ok None
  else
    let* declared = declared structure in
    let ctor name args =
      let raven = String.uncapitalize name in
      {
        Datatypes.ocaml = name;
        raven;
        fields = List.mapi args ~f:(fun i _ -> Printf.sprintf "%s_%d" raven i);
        args;
      }
    in
    Ok
      (Some
         {
           Datatypes.option with
           paths = [ Predef.path_exn ];
           module_name = Fresh_names.fresh "Exn";
           ctors =
             List.map predefined ~f:(fun name -> ctor name [])
             @ List.map declared ~f:(fun d -> ctor d.name d.args);
           at = Location.none;
         })

(** The exception that raising [e] raises, if [e] names it by its constructor. *)
let named (e : Typedtree.expression) =
  match e.exp_desc with
  | Texp_construct (_, cstr, _) -> (
      match cstr.cstr_tag with Cstr_extension _ -> Some cstr.cstr_name | _ -> None)
  | _ -> None

(** The argument of [e] if [e] raises it, as [raise e] or [raise_notrace e]. *)
let raised_argument (e : Typedtree.expression) =
  match e.exp_desc with
  | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, [ (_, Arg argument) ])
    when Option.exists (Translate_context.stdlib_name path) ~f:(fun name ->
             String.equal name "raise" || String.equal name "raise_notrace") ->
      Some argument
  | _ -> None

(** The exceptions that handler patterns [patterns] catch whatever their payloads, and
    whether one catches every exception. *)
let handled (patterns : Typedtree.pattern list) =
  let rec irrefutable (p : Typedtree.pattern) =
    match p.pat_desc with
    | Tpat_any | Tpat_var _ -> true
    | Tpat_alias (q, _, _, _, _) -> irrefutable q
    | Tpat_tuple ps -> List.for_all ps ~f:(fun (_, q) -> irrefutable q)
    | _ -> false
  in
  let rec catches (p : Typedtree.pattern) =
    match p.pat_desc with
    | Tpat_any | Tpat_var _ -> ([], true)
    | Tpat_alias (q, _, _, _, _) -> catches q
    | Tpat_construct (_, cstr, args, _) when List.for_all args ~f:irrefutable -> (
        match cstr.cstr_tag with
        | Cstr_extension _ -> ([ cstr.cstr_name ], false)
        | _ -> ([], false))
    | Tpat_or (a, b, _) ->
        let a, all_a = catches a and b, all_b = catches b in
        (a @ b, all_a || all_b)
    | _ -> ([], false)
  in
  List.fold patterns ~init:([], false) ~f:(fun (names, all) p ->
      let more, every = catches p in
      (names @ more, all || every))

type use =
  | Raise of string option * Location.t
      (** A raise of the exception named, or of an exception value. *)
  | Reraise of uses * Location.t
      (** A raise of what a handler caught, from its protected part's uses. *)
  | Call of Path.t * Location.t
  | Handled of { protected : uses; handled : string list; catch_all : bool; cases : uses }

and uses = (use * bool) list
(** Uses, each with whether it is in a loop. *)

(** The raises and calls of [body], outside the local functions it defines. *)
let uses (body : Typedtree.expression) =
  let rec scan caught loops (e : Typedtree.expression) : uses =
    let sub = scan caught loops in
    match (e.exp_desc, raised_argument e) with
    | _, Some argument ->
        let raised =
          match (named argument, argument.exp_desc) with
          | Some name, _ -> Raise (Some name, e.exp_loc)
          | None, Texp_ident (Pident id, _, _) -> (
              match List.Assoc.find caught id ~equal:Ident.same with
              | Some protected -> Reraise (protected, e.exp_loc)
              | None -> Raise (None, e.exp_loc))
          | None, _ -> Raise (None, e.exp_loc)
        in
        sub argument @ [ (raised, loops > 0) ]
    | Texp_function _, None -> []
    | Texp_try (protected, cases, _), None ->
        let protected = sub protected in
        let handled, catch_all =
          handled
            (List.map cases ~f:(fun (c : Typedtree.value Typedtree.case) -> c.c_lhs))
        in
        let cases =
          List.concat_map cases ~f:(fun (c : Typedtree.value Typedtree.case) ->
              let caught =
                List.map (Typedtree.pat_bound_idents c.c_lhs) ~f:(fun id ->
                    (id, protected))
                @ caught
              in
              scan caught loops c.c_rhs)
        in
        [ (Handled { protected; handled; catch_all; cases }, loops > 0) ]
    | Texp_match (scrutinee, match_cases, _, _), None
      when List.exists match_cases ~f:(fun (c : Typedtree.computation Typedtree.case) ->
               Option.is_some (snd (Typedtree.split_pattern c.c_lhs))) ->
        let protected = sub scrutinee in
        let split =
          List.map match_cases ~f:(fun (c : Typedtree.computation Typedtree.case) ->
              (Typedtree.split_pattern c.c_lhs, c.c_rhs))
        in
        let exception_cases =
          List.filter_map split ~f:(fun ((_, p), rhs) ->
              Option.map p ~f:(fun p -> (p, rhs)))
        in
        let handled, catch_all = handled (List.map exception_cases ~f:fst) in
        let cases =
          List.concat_map exception_cases ~f:(fun (p, rhs) ->
              let caught =
                List.map (Typedtree.pat_bound_idents p) ~f:(fun id -> (id, protected))
                @ caught
              in
              scan caught loops rhs)
        in
        (Handled { protected; handled; catch_all; cases }, loops > 0)
        :: List.concat_map split ~f:(fun ((value, _), rhs) ->
            if Option.is_some value then sub rhs else [])
    | (Texp_while _ | Texp_for _), None -> children (scan caught (loops + 1)) e
    | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _), None ->
        (Call (path, e.exp_loc), loops > 0) :: children sub e
    | _ -> children sub e
  and children f (e : Typedtree.expression) =
    let found = ref [] in
    let iterator =
      {
        Tast_iterator.default_iterator with
        expr = (fun _ child -> found := f child :: !found);
      }
    in
    Tast_iterator.default_iterator.expr iterator e;
    List.concat (List.rev !found)
  in
  scan [] 0 body

let union = Translate_context.union_raises

(** The exceptions of [contract]'s [raises] and [atomic raises] clauses. *)
let declared_raises (contract : Caravan_spec.Spec_ast.contract) =
  Translate_context.State_monad.Raises
    (List.filter_map
       (List.map contract.raises ~f:fst @ List.map contract.atomic_raises ~f:fst)
       ~f:(fun (p : Caravan_spec.Spec_ast.pat) ->
         match p.pat_desc with
         | Pconstr (Qid id, _) -> Some id.pid_str
         | Pconstr (Qdot (_, id), _) -> Some id.pid_str
         | _ -> None)
    |> List.dedup_and_sort ~compare:String.compare)

(** The exceptions that [uses] may raise, with [callee] the exceptions of a call. *)
let rec raised ~callee (uses : uses) =
  List.fold uses ~init:(Translate_context.State_monad.Raises []) ~f:(fun set (use, _) ->
      union set
        (match use with
        | Raise (Some name, _) -> Raises [ name ]
        | Raise (None, _) -> Raises_any
        | Reraise (protected, _) -> raised ~callee protected
        | Call (path, _) -> callee path
        | Handled { protected; handled; catch_all; cases } ->
            union
              (Translate_context.unhandled (raised ~callee protected) ~handled ~catch_all)
              (raised ~callee cases)))

(** The exceptions each procedure may raise, for those that may raise any: [procedures]
    gives each procedure's name, contract and body, and [resolve] the procedure a path
    calls from it. A function with a contract raises what its [raises] clauses say; one
    without raises what its body raises and its calls may raise. *)
let raise_sets procedures ~resolve =
  let module S = Translate_context.State_monad in
  let bodies =
    List.map procedures ~f:(fun (name, contract, body) -> (name, contract, uses body))
  in
  let initial =
    List.map bodies ~f:(fun (name, contract, _) ->
        ( name,
          match (contract : Caravan_spec.Spec_ast.contract option) with
          | Some contract -> declared_raises contract
          | None -> S.Raises [] ))
  in
  let same left right =
    match (left, right) with
    | S.Raises_any, S.Raises_any -> true
    | Raises a, Raises b -> List.equal String.equal a b
    | _ -> false
  in
  let rec fixed_point sets =
    let next =
      List.map bodies ~f:(fun (name, contract, uses) ->
          match contract with
          | Some _ -> (name, List.Assoc.find_exn sets name ~equal:String.equal)
          | None ->
              let callee path =
                Option.value_map (resolve name path) ~default:(S.Raises [])
                  ~f:(fun callee ->
                    Option.value
                      (List.Assoc.find sets callee ~equal:String.equal)
                      ~default:(S.Raises []))
              in
              (name, raised ~callee uses))
    in
    if List.for_all2_exn sets next ~f:(fun (_, a) (_, b) -> same a b) then sets
    else fixed_point next
  in
  List.filter (fixed_point initial) ~f:(fun (_, set) ->
      match set with S.Raises [] -> false | _ -> true)

let outcome_term ~at =
  S.mk_term (Tvar (Qid (S.mk_id ~loc:at Translate_context.outcome_name))) at

let pattern ~at desc = { S.pat_desc = desc; pat_loc = at }

let constructor_pattern ~at name argument =
  pattern ~at (Pconstr (Qid (S.mk_id ~loc:at name), argument))

(** The postcondition [t] of a function that may raise, holding when it returns. *)
let on_return (t : S.term) =
  let at = t.term_loc in
  S.mk_term
    (Tmatch
       ( outcome_term ~at,
         [
           (constructor_pattern ~at "None" None, t);
           (pattern ~at Pwild, S.mk_term Ttrue at);
         ] ))
    at

(** The postconditions of a function, or a loop, that may raise the exceptions [set], with
    its [raises] clauses [clauses]: what holds when it raises each, and that it raises no
    other. *)
let raises_postconditions ?(only = true) types ~at clauses set =
  let some p = constructor_pattern ~at "Some" (Some p) in
  let true_ = S.mk_term Ttrue at in
  let holds =
    List.filter_map clauses ~f:(fun (p, post) ->
        Option.map post ~f:(fun post ->
            S.mk_term
              (Tmatch (outcome_term ~at, [ (some p, post); (pattern ~at Pwild, true_) ]))
              at))
  in
  let raised =
    match (clauses, set) with
    | _ :: _, _ -> Some (List.map clauses ~f:fst)
    | [], Translate_context.State_monad.Raises names ->
        Some
          (List.map names ~f:(fun name ->
               let argument =
                 match Datatypes.find_ctor types name with
                 | Some (_, { fields = _ :: _; _ }) -> Some (pattern ~at Pwild)
                 | _ -> None
               in
               constructor_pattern ~at name argument))
    | [], Translate_context.State_monad.Raises_any -> None
  in
  let only_raised =
    Option.map raised ~f:(fun patterns ->
        S.mk_term
          (Tmatch
             ( outcome_term ~at,
               (constructor_pattern ~at "None" None, true_)
               :: List.map patterns ~f:(fun p -> (some p, true_))
               @ [ (pattern ~at Pwild, S.mk_term Tfalse at) ] ))
          at)
  in
  holds @ if only then Option.to_list only_raised else []
