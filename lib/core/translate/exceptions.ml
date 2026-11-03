(** OCaml's exceptions, as the constructors of one Raven data type for [exn]: those the
    program declares, at the top level or in modules, and the predefined ones it may
    raise. *)

open Base

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

type use =
  | Raise of string option * Location.t
      (** A raise of the exception named, or of an exception value. *)
  | Call of Path.t * Location.t

(** The raises and calls of [body], outside the local functions it defines, each with
    whether it is in a loop. *)
let uses (body : Typedtree.expression) =
  let found = ref [] and loops = ref 0 in
  let record use = found := (use, !loops > 0) :: !found in
  let iterator =
    {
      Tast_iterator.default_iterator with
      expr =
        (fun self e ->
          match (e.exp_desc, raised_argument e) with
          | _, Some argument ->
              record (Raise (named argument, e.exp_loc));
              self.expr self argument
          | Texp_function _, None -> ()
          | (Texp_while _ | Texp_for _), None ->
              Int.incr loops;
              Tast_iterator.default_iterator.expr self e;
              Int.decr loops
          | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _), None ->
              record (Call (path, e.exp_loc));
              Tast_iterator.default_iterator.expr self e
          | _ -> Tast_iterator.default_iterator.expr self e);
    }
  in
  iterator.expr iterator body;
  List.rev !found

let union left right =
  match (left, right) with
  | Translate_context.State_monad.Raises_any, _
  | _, Translate_context.State_monad.Raises_any ->
      Translate_context.State_monad.Raises_any
  | Raises a, Raises b -> Raises (List.dedup_and_sort (a @ b) ~compare:String.compare)

(** The exceptions of [contract]'s [raises] clauses. *)
let declared_raises (contract : Caravan_spec.Spec_ast.contract) =
  Translate_context.State_monad.Raises
    (List.filter_map contract.raises ~f:(fun ((p : Caravan_spec.Spec_ast.pat), _) ->
         match p.pat_desc with
         | Pconstr (Qid id, _) -> Some id.pid_str
         | Pconstr (Qdot (_, id), _) -> Some id.pid_str
         | _ -> None))

(** The exceptions each procedure may raise, for those that may raise any: [procedures]
    gives each procedure's name, contract and body, and [resolve] the procedure a path
    calls from it. A function with a contract raises what its [raises] clauses say; one
    without raises what its body raises and its calls may raise. *)
let raise_sets procedures ~resolve =
  let module S = Translate_context.State_monad in
  let direct =
    List.map procedures ~f:(fun (name, contract, body) ->
        let uses = uses body in
        ( name,
          contract,
          List.fold uses ~init:(S.Raises []) ~f:(fun set (use, _) ->
              match use with
              | Raise (Some e, _) -> union set (S.Raises [ e ])
              | Raise (None, _) -> union set S.Raises_any
              | Call _ -> set),
          List.filter_map uses ~f:(fun (use, _) ->
              match use with Call (path, _) -> resolve name path | Raise _ -> None) ))
  in
  let initial =
    List.map direct ~f:(fun (name, contract, own, _) ->
        ( name,
          match (contract : Caravan_spec.Spec_ast.contract option) with
          | Some contract -> declared_raises contract
          | None -> own ))
  in
  let same left right =
    match (left, right) with
    | S.Raises_any, S.Raises_any -> true
    | Raises a, Raises b -> List.equal String.equal a b
    | _ -> false
  in
  let rec fixed_point sets =
    let next =
      List.map direct ~f:(fun (name, contract, own, callees) ->
          match contract with
          | Some _ -> (name, List.Assoc.find_exn sets name ~equal:String.equal)
          | None ->
              ( name,
                List.fold callees ~init:own ~f:(fun set callee ->
                    Option.value_map
                      (List.Assoc.find sets callee ~equal:String.equal)
                      ~default:set ~f:(union set)) ))
    in
    if List.for_all2_exn sets next ~f:(fun (_, a) (_, b) -> same a b) then sets
    else fixed_point next
  in
  List.filter (fixed_point initial) ~f:(fun (_, set) ->
      match set with S.Raises [] -> false | _ -> true)
