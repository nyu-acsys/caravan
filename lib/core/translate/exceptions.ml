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

type witness_argument =
  | Constructor of string  (** A witness constructor. *)
  | Forwarded  (** The caller's own witness. *)

type use =
  | Raise of string option * Location.t
      (** A raise of the exception named, or of an exception value. *)
  | Reraise of uses * Location.t
      (** A raise of what a handler caught, from its protected part's uses. *)
  | Call of Path.t * Location.t * witness_argument option
  | Handled of { protected : uses; handled : string list; catch_all : bool; cases : uses }
  | Witness_cases of (string list option * uses) list
      (** A match on the function's witness: its cases, each with the constructors it
          matches, [None] for any. *)

and uses = (use * bool) list
(** Uses, each with whether it is in a loop. *)

(** The constructors that [p] matches, [None] if any. *)
let rec matched_constructors (p : Typedtree.pattern) =
  match p.pat_desc with
  | Tpat_construct (_, cstr, _, _) -> Some [ cstr.cstr_name ]
  | Tpat_or (a, b, _) ->
      Option.map2 (matched_constructors a) (matched_constructors b) ~f:( @ )
  | Tpat_alias (p, _, _, _, _) -> matched_constructors p
  | _ -> None

(** The raises and calls of [body], outside the local functions it defines; [witness] is
    the function's witness parameter, whose matches record their cases. *)
let uses ?witness (body : Typedtree.expression) =
  let rec scan caught loops (e : Typedtree.expression) : uses =
    let sub = scan caught loops in
    match (e.exp_desc, raised_argument e) with
    | Texp_match ({ exp_desc = Texp_ident (Pident id, _, _); _ }, cases, [], _), None
      when Option.exists witness ~f:(Ident.same id) ->
        [
          ( Witness_cases
              (List.map cases ~f:(fun (c : Typedtree.computation Typedtree.case) ->
                   let constructors =
                     match Typedtree.split_pattern c.c_lhs with
                     | Some p, None -> matched_constructors p
                     | _ -> None
                   in
                   ( constructors,
                     Option.value_map c.c_guard ~default:[] ~f:sub @ sub c.c_rhs ))),
            loops > 0 );
        ]
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
    | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, args), None ->
        let witness_argument =
          List.find_map args ~f:(fun (_, arg) ->
              match arg with
              | Typedtree.Arg { exp_desc = Texp_construct (_, cstr, []); _ }
                when cstr.cstr_generalized ->
                  Some (Constructor cstr.cstr_name)
              | Arg { exp_desc = Texp_ident (Pident id, _, _); _ }
                when Option.exists witness ~f:(Ident.same id) ->
                  Some Forwarded
              | _ -> None)
        in
        (Call (path, e.exp_loc, witness_argument), loops > 0) :: children sub e
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

(** The exceptions that [uses] may raise, with [callee] the exceptions of a call; only in
    the cases for the witness constructor [constructor] if given. *)
let rec raised ?constructor ~callee (uses : uses) =
  let raised = raised ?constructor ~callee in
  List.fold uses ~init:(Translate_context.State_monad.Raises []) ~f:(fun set (use, _) ->
      union set
        (match use with
        | Raise (Some name, _) -> Raises [ name ]
        | Raise (None, _) -> Raises_any
        | Reraise (protected, _) -> raised protected
        | Call (path, _, witness_argument) ->
            (* A call passing the caller's witness raises what the callee does for the
               same constructor. *)
            let witness_argument =
              match (witness_argument, constructor) with
              | Some Forwarded, Some c -> Some (Constructor c)
              | Some Forwarded, None -> None
              | argument, _ -> argument
            in
            callee path witness_argument
        | Handled { protected; handled; catch_all; cases } ->
            union
              (Translate_context.unhandled (raised protected) ~handled ~catch_all)
              (raised cases)
        | Witness_cases cases ->
            List.fold cases ~init:(Translate_context.State_monad.Raises [])
              ~f:(fun set (constructors, uses) ->
                let reached =
                  match (constructor, constructors) with
                  | Some c, Some cs -> List.mem cs c ~equal:String.equal
                  | None, _ | _, None -> true
                in
                if reached then union set (raised uses) else set)))

(** The exceptions in both [left] and [right]. *)
let intersection left right =
  match (left, right) with
  | Translate_context.State_monad.Raises_any, set
  | set, Translate_context.State_monad.Raises_any ->
      set
  | Raises a, Raises b -> Raises (List.filter a ~f:(List.mem b ~equal:String.equal))

(** The exceptions each procedure may raise, for those that may raise any: [procedures]
    gives each procedure's name, contract, body and witness parameter with its
    constructors, and [resolve] the procedure a path calls from it. A function with a
    contract raises what its [raises] clauses say; one without raises what its body raises
    and its calls may raise. Also, per witness constructor, what each function with a
    witness parameter raises when called with it. *)
let raise_sets procedures ~resolve =
  let module S = Translate_context.State_monad in
  let bodies =
    List.map procedures ~f:(fun (name, contract, body, witness) ->
        ( name,
          (contract : Caravan_spec.Spec_ast.contract option),
          uses ?witness:(Option.map witness ~f:fst) body,
          Option.map witness ~f:snd ))
  in
  let same left right =
    match (left, right) with
    | S.Raises_any, S.Raises_any -> true
    | Raises a, Raises b -> List.equal String.equal a b
    | _ -> false
  in
  (* What each procedure raises, and per witness constructor what those over a witness
     do, from none: every exception raised comes from a raise. *)
  let rec fixed_point (sets, by_constructor) =
    let callee name path witness_argument =
      Option.value_map (resolve name path) ~default:(S.Raises []) ~f:(fun callee ->
          let constructor_set =
            match witness_argument with
            | Some (Constructor c) ->
                Option.bind (List.Assoc.find by_constructor callee ~equal:String.equal)
                  ~f:(fun sets -> List.Assoc.find sets c ~equal:String.equal)
            | Some Forwarded | None -> None
          in
          match constructor_set with
          | Some set -> set
          | None ->
              Option.value
                (List.Assoc.find sets callee ~equal:String.equal)
                ~default:(S.Raises []))
    in
    let declared_or contract inferred =
      match contract with
      | Some contract -> intersection (declared_raises contract) (Lazy.force inferred)
      | None -> Lazy.force inferred
    in
    let next_sets =
      List.map bodies ~f:(fun (name, contract, uses, _) ->
          match contract with
          | Some contract -> (name, declared_raises contract)
          | None -> (name, raised ~callee:(callee name) uses))
    in
    let next_by_constructor =
      List.filter_map bodies ~f:(fun (name, contract, uses, constructors) ->
          Option.map constructors ~f:(fun constructors ->
              ( name,
                List.map constructors ~f:(fun constructor ->
                    ( constructor,
                      declared_or contract
                        (lazy (raised ~constructor ~callee:(callee name) uses)) )) )))
    in
    let stable =
      List.for_all2_exn sets next_sets ~f:(fun (_, a) (_, b) -> same a b)
      && List.for_all2_exn by_constructor next_by_constructor ~f:(fun (_, a) (_, b) ->
          List.for_all2_exn a b ~f:(fun (_, a) (_, b) -> same a b))
    in
    if stable then (sets, by_constructor) else fixed_point (next_sets, next_by_constructor)
  in
  let initial =
    ( List.map bodies ~f:(fun (name, contract, _, _) ->
          ( name,
            match contract with
            | Some contract -> declared_raises contract
            | None -> S.Raises [] )),
      List.filter_map bodies ~f:(fun (name, _, _, constructors) ->
          Option.map constructors ~f:(fun constructors ->
              (name, List.map constructors ~f:(fun c -> (c, S.Raises []))))) )
  in
  let sets, by_constructor = fixed_point initial in
  ( List.filter sets ~f:(fun (_, set) -> match set with S.Raises [] -> false | _ -> true),
    by_constructor )

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
