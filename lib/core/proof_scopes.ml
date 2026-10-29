(** Proof declarations attached to the implementation scopes of source modules. *)

open Base
module S = Caravan_spec.Spec_ast

let ( let* ) = Result.( >>= )

type scope = {
  owner : Path.t option;
  declaration_id : Ident.t option;
  namespace : string list;
  parent : Path.t option;
  environment : Env.t;
  parameters : Typedtree.functor_parameter list;
  structure : Typedtree.structure;
  public_type : Types.module_type option;
  sealed : bool;
  definition : S.qualid option;
  source_location : Location.t;
  proof_location : Location.t option;
}

type entry = { id : Ident.t; name : S.id; declaration : S.proof_decl; scope : scope }
type t = { root : scope; scopes : scope list; declarations : entry list }

let name = function
  | S.Proof_module { module_name; _ } -> module_name
  | Proof_definition { module_name; _ } -> module_name
  | Proof_predicate p -> p.pred_name
  | Proof_type { type_name; _ } -> type_name
  | Proof_resource { resource_name; _ } -> resource_name
  | Proof_au { au_name; _ } -> au_name
  | Proof_field { field_name; _ } -> field_name
  | Proof_function { function_name; _ } -> function_name
  | Proof_lemma { lemma_name; _ } -> lemma_name
  | Proof_state { state_name; _ } -> state_name
  | Proof_invariant { inv_name; _ } -> inv_name
  | Proof_view { view_name; _ } -> view_name
  | Proof_action { action_name; _ } -> action_name

let same_scope a b = Option.equal Ident.same a.declaration_id b.declaration_id

let declarations_in inventory scope =
  List.filter inventory.declarations ~f:(fun entry -> same_scope entry.scope scope)

let find_namespace inventory namespace =
  List.find inventory.scopes ~f:(fun scope ->
      List.equal String.equal scope.namespace namespace)

let find_owner inventory owner =
  List.find inventory.scopes ~f:(fun scope -> Option.equal Path.same scope.owner owner)

let rec canonical_owner inventory path =
  match path with
  | Path.Pident id ->
      Option.value_map
        (List.find inventory.scopes ~f:(fun scope ->
             Option.exists scope.declaration_id ~f:(Ident.same id)))
        ~default:path
        ~f:(fun scope -> Option.value scope.owner ~default:path)
  | Pdot (parent, name) -> Path.Pdot (canonical_owner inventory parent, name)
  | Papply (fn, argument) ->
      Path.Papply (canonical_owner inventory fn, canonical_owner inventory argument)
  | Pextra_ty (path, extra) -> Path.Pextra_ty (canonical_owner inventory path, extra)

let map_environments inventory ~f =
  let update scope = { scope with environment = f scope } in
  {
    root = update inventory.root;
    scopes = List.map inventory.scopes ~f:update;
    declarations =
      List.map inventory.declarations ~f:(fun entry ->
          { entry with scope = update entry.scope });
  }

let compiler_error ~at exn =
  Option.value (Report.of_exn exn)
    ~default:(Report.error Type at (Stdlib.Printexc.to_string exn))

let compiler ~at f = try Ok (f ()) with exn -> Error (compiler_error ~at exn)

let rec longident = function
  | S.Qid id -> Longident.Lident id.pid_str
  | Qdot (parent, id) ->
      Longident.Ldot
        ( { txt = longident parent; loc = S.qualid_loc parent },
          { txt = id.pid_str; loc = id.pid_loc } )

let parameter_location = function
  | S.Proof_named_parameter (name, _) -> name.pid_loc
  | Proof_unit_parameter at -> at

let module_type_path environment name =
  let at = S.qualid_loc name in
  try Ok (fst (Env.find_modtype_by_name (longident name) environment)) with
  | Stdlib.Not_found ->
      Error
        (Report.error Type at
           ("Unknown module type in proof header: "
           ^ Qualified_name.to_string (Qualified_name.of_spec name)))
  | exn -> Error (compiler_error ~at exn)

let check_parameter source proof =
  let error at message = Error (Report.error Type at message) in
  match (source, proof) with
  | Typedtree.Unit, S.Proof_unit_parameter _ -> Ok ()
  | ( Named (Some _, { txt = Some source_name; _ }, module_type),
      Proof_named_parameter (proof_name, proof_type) ) ->
      if not (String.equal source_name proof_name.pid_str) then
        error proof_name.pid_loc
          (Printf.sprintf "This proof parameter must be named %s" source_name)
      else
        begin match module_type.mty_desc with
        | Tmty_ident (source_path, _) ->
            let at = S.qualid_loc proof_type in
            let environment = module_type.mty_env in
            let* proof_path = module_type_path environment proof_type in
            let* same =
              compiler ~at (fun () ->
                  Path.same
                    (Env.normalize_modtype_path environment source_path)
                    (Env.normalize_modtype_path environment proof_path))
            in
            if same then Ok ()
            else
              error at "The proof parameter must name the source parameter's module type"
        | Tmty_signature _ | Tmty_functor _ | Tmty_with _ | Tmty_typeof _ | Tmty_alias _
          ->
            Report.unsupported proof_name.pid_loc
              "A proof block for a functor parameter without a named module type"
        end
  | Named ((None | Some _), { txt = None; _ }, _), _ ->
      Report.unsupported (parameter_location proof)
        "A proof block for an anonymous functor parameter"
  | Unit, Proof_named_parameter _ | Named _, Proof_unit_parameter _ ->
      error (parameter_location proof)
        "The proof parameter kind does not match the source functor"
  | Named (None, { txt = Some _; _ }, _), Proof_named_parameter _ ->
      Report.unsupported (parameter_location proof)
        "A proof block for an anonymous functor parameter"

let check_parameters ~at source proof =
  match List.zip source proof with
  | Unequal_lengths ->
      Error
        (Report.error Type at "The proof module must repeat all source functor parameters")
  | Ok pairs ->
      List.fold_result pairs ~init:() ~f:(fun () (source, proof) ->
          check_parameter source proof)

let direct_module structure name =
  List.find_map (List.rev structure.Typedtree.str_items) ~f:(fun item ->
      match item.Typedtree.str_desc with
      | Tstr_module ({ mb_name = { txt = Some candidate; _ }; _ } as declaration)
        when String.equal candidate name ->
          Some declaration
      | Tstr_value _ | Tstr_primitive _ | Tstr_type _ | Tstr_typext _ | Tstr_exception _
      | Tstr_module _ | Tstr_recmodule _ | Tstr_modtype _ | Tstr_open _ | Tstr_class _
      | Tstr_class_type _ | Tstr_include _ | Tstr_attribute _ | Tstr_eval _ ->
          None)

let implementation ~at expression =
  let rec body reversed (expression : Typedtree.module_expr) =
    match expression.mod_desc with
    | Tmod_constraint (expression, _, _, _) -> body reversed expression
    | Tmod_functor (parameter, expression) -> body (parameter :: reversed) expression
    | Tmod_structure structure -> Ok (List.rev reversed, structure)
    | Tmod_ident _ ->
        Error
          (Report.error Type at
             "A proof module block must attach to a definition, not a module alias")
    | Tmod_apply _ | Tmod_apply_unit _ ->
        Error
          (Report.error Type at
             "A functor application inherits its proof from the functor definition")
    | Tmod_unpack _ -> Report.unsupported at "A proof block for a first-class module"
  in
  body [] expression

let child_scope ?(check_header = true) parent (name : S.id) parameters location =
  match direct_module parent.structure name.pid_str with
  | None ->
      Error
        (Report.error Type name.pid_loc
           (Printf.sprintf "No source module definition named %s in this scope"
              name.pid_str))
  | Some { mb_id = None; _ } ->
      Report.unsupported name.pid_loc "A proof block for an anonymous module"
  | Some ({ mb_id = Some id; mb_expr; _ } as declaration) ->
      let* source_parameters, structure = implementation ~at:name.pid_loc mb_expr in
      let* () =
        if check_header then
          check_parameters ~at:name.pid_loc source_parameters parameters
        else Ok ()
      in
      let owner =
        Option.value_map parent.owner ~default:(Path.Pident id) ~f:(fun parent ->
            Path.Pdot (parent, name.pid_str))
      in
      Ok
        {
          owner = Some owner;
          declaration_id = Some id;
          namespace = parent.namespace @ [ name.pid_str ];
          parent = parent.owner;
          environment = structure.str_final_env;
          parameters = source_parameters;
          structure;
          public_type = Some mb_expr.mod_type;
          sealed = (match mb_expr.mod_desc with Tmod_constraint _ -> true | _ -> false);
          definition = None;
          source_location = declaration.mb_loc;
          proof_location = Some location;
        }

let definition_scope parent (name : S.id) interface location =
  let at = name.pid_loc in
  let* id, public_type =
    match Env.find_module_by_name (Longident.Lident name.pid_str) parent.environment with
    | Pident id, declaration -> Ok (id, declaration.md_type)
    | _ -> Error (Report.error Type at "A proof-defined module must be local")
  in
  let structure, _, _, _, _ = Typemod.type_structure parent.environment [] in
  Ok
    {
      owner =
        Some
          (Option.value_map parent.owner ~default:(Path.Pident id) ~f:(fun owner ->
               Path.Pdot (owner, name.pid_str)));
      declaration_id = Some id;
      namespace = parent.namespace @ [ name.pid_str ];
      parent = parent.owner;
      environment = parent.environment;
      parameters = [];
      structure;
      public_type = Some public_type;
      sealed = true;
      definition = Some interface;
      source_location = location;
      proof_location = Some location;
    }

let resolve_prepared ?(location = Location.none) ~environment ~state ~prepare_definition
    (structure : Typedtree.structure) declarations =
  let root =
    {
      owner = None;
      declaration_id = None;
      namespace = [];
      parent = None;
      environment;
      parameters = [];
      structure;
      public_type = None;
      sealed = false;
      definition = None;
      source_location = location;
      proof_location = None;
    }
  in
  let replace_scope scope scopes =
    List.map scopes ~f:(fun previous ->
        if same_scope scope previous then scope else previous)
  in
  let rec collect state scope scopes entries declarations =
    List.fold_result declarations ~init:(state, scope, scopes, entries)
      ~f:(fun (state, scope, scopes, entries) declaration ->
        match declaration with
        | S.Proof_module
            { module_name; module_parameters; module_declarations; module_loc } ->
            let* nested = child_scope scope module_name module_parameters module_loc in
            begin match List.find scopes ~f:(same_scope nested) with
            | Some previous ->
                Error
                  (Report.error Type module_name.pid_loc
                     ~related:
                       (Option.to_list
                          (Option.map previous.proof_location ~f:(fun at ->
                               (at, "Its other proof block"))))
                     "A source module has more than one proof block")
            | None ->
                let* state, _, scopes, entries =
                  collect state nested (nested :: scopes) entries module_declarations
                in
                Ok (state, scope, scopes, entries)
            end
        | S.Proof_definition
            { module_name; module_interface; module_declarations; module_loc } ->
            let* state, scope =
              prepare_definition state scope module_name module_interface
            in
            let scopes = replace_scope scope scopes in
            let* nested =
              definition_scope scope module_name module_interface module_loc
            in
            begin match List.find scopes ~f:(same_scope nested) with
            | Some _ ->
                Error
                  (Report.error Type module_name.pid_loc
                     "A proof-defined module has more than one definition")
            | None ->
                let header =
                  {
                    id = Ident.create_local module_name.pid_str;
                    name = module_name;
                    declaration;
                    scope;
                  }
                in
                let* state, _, scopes, entries =
                  collect state nested (nested :: scopes) (header :: entries)
                    module_declarations
                in
                Ok (state, scope, scopes, entries)
            end
        | declaration ->
            let name = name declaration in
            let entry =
              { id = Ident.create_local name.pid_str; name; declaration; scope }
            in
            Ok (state, scope, scopes, entry :: entries))
  in
  let* state, root, scopes, declarations = collect state root [ root ] [] declarations in
  Ok (state, { root; scopes = List.rev scopes; declarations = List.rev declarations })

let resolve ?location ~environment structure declarations =
  Result.map
    (resolve_prepared ?location ~environment ~state:()
       ~prepare_definition:(fun () scope _ _ -> Ok ((), scope))
       structure declarations)
    ~f:snd

(** Module owners containing a source annotation, including scopes without proof blocks.
*)
let owner_paths_at inventory (location : Location.t) =
  let inside outer = Declaration_scope.contains outer location in
  let rec structure parent (body : Typedtree.structure) =
    List.concat_map body.str_items ~f:(fun item ->
        match item.Typedtree.str_desc with
        | Tstr_module
            { mb_id = Some id; mb_name = { txt = Some name; _ }; mb_expr; mb_loc; _ }
          when inside mb_loc ->
            let path =
              Option.value_map parent ~default:(Path.Pident id) ~f:(fun parent ->
                  Path.Pdot (parent, name))
            in
            [ Path.Pident id; path ] :: expression (Some path) mb_expr
        | _ -> [])
  and expression parent (body : Typedtree.module_expr) =
    match body.mod_desc with
    | Tmod_structure body -> structure parent body
    | Tmod_functor (_, body) | Tmod_constraint (body, _, _, _) -> expression parent body
    | _ -> []
  in
  structure None inventory.root.structure

let owners_at inventory location = List.concat (owner_paths_at inventory location)

let innermost_owners_at inventory location =
  Option.value (List.last (owner_paths_at inventory location)) ~default:[]
