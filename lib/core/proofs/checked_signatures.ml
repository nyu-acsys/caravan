open Base
module Ast = Raven_api.Ast

type typ =
  | Bool
  | Int
  | Real
  | Ref
  | Tuple of typ list
  | Set of typ
  | FinSet of typ
  | Map of typ * typ
  | Named of string list * typ list
  | Other of string

type parameter = { name : string; interface : string list }

type operation = {
  name : string;
  inputs : (string * typ) list;
  outputs : (string * typ) list;
}

type type_member = {
  name : string;
  rep : bool;
  definition : typ option;
  constructors : operation list;
  destructors : operation list;
}

type module_signature = {
  path : string list;
  interface : bool;
  parameters : parameter list;
  implements : string list list;
  required_members : (string * string) list;
  types : type_member list;
  operations : operation list;
  constants : (string * typ) list;
}

let name = Ast.Ident.name
let qid_path qid = List.map (Ast.QualIdent.shown_path qid) ~f:name

let rec typ (Ast.Type.App (constr, args, _)) =
  match (constr, args) with
  | Ast.Type.Bool, [] -> Bool
  | Ast.Type.Int, [] -> Int
  | Ast.Type.Real, [] -> Real
  | Ast.Type.Ref, [] -> Ref
  | Ast.Type.Prod, elements -> Tuple (List.map elements ~f:typ)
  | Ast.Type.Map, [ element; Ast.Type.App (Ast.Type.Bool, [], _) ] -> Set (typ element)
  | Ast.Type.Map, [ key; value ] -> Map (typ key, typ value)
  | Ast.Type.FinSet, [ element ] -> FinSet (typ element)
  | Ast.Type.Var qualified, arguments | Ast.Type.Data (qualified, _), arguments ->
      Named (qid_path qualified, List.map arguments ~f:typ)
  | _ -> Other (Ast.Type.to_name constr)

let vars decls =
  List.map decls ~f:(fun (decl : Ast.Type.var_decl) ->
      (name decl.var_name, typ decl.var_type))

let type_member path (def : Ast.Module.type_def) =
  let type_name = name def.type_def_name in
  let result = Named (path @ [ type_name ], []) in
  let constructors, destructors, definition =
    match def.type_def_expr with
    | Some (Ast.Type.App (Ast.Type.Data (_, variants), _, _)) ->
        let constructors =
          List.map variants ~f:(fun (variant : Ast.Type.variant_decl) ->
              {
                name = name variant.variant_name;
                inputs = vars variant.variant_args;
                outputs = [ ("result", result) ];
              })
        in
        let destructors =
          List.concat_map variants ~f:(fun (variant : Ast.Type.variant_decl) ->
              List.map variant.variant_args ~f:(fun (arg : Ast.Type.var_decl) ->
                  {
                    name = name arg.var_name;
                    inputs = [ ("value", result) ];
                    outputs = [ ("result", typ arg.var_type) ];
                  }))
        in
        (constructors, destructors, None)
    | Some definition -> ([], [], Some (typ definition))
    | None -> ([], [], None)
  in
  { name = type_name; rep = def.type_def_rep; definition; constructors; destructors }

let operation (call : Ast.Callable.t) =
  let decl = call.call_decl in
  {
    name = name (Ast.Callable.source_ident call);
    inputs = vars decl.call_decl_formals;
    outputs = vars decl.call_decl_returns;
  }

let required_members (md : Ast.Module.t) =
  List.filter_map md.mod_def ~f:(function
    | Ast.Module.SymbolDef symbol ->
        Option.map
          (Ast.ProgUtils.non_rep_abstract_member ~rep_ident:md.mod_decl.mod_decl_rep
             symbol) ~f:(fun (kind, member) -> (kind, name member))
    | Ast.Module.Import _ -> None)

let rec modules path (md : Ast.Module.t) =
  let path = path @ [ name md.mod_decl.mod_decl_name ] in
  let open Ast.Module in
  let types, operations, constants, nested =
    List.fold md.mod_def ~init:([], [], [], [])
      ~f:(fun (types, operations, constants, nested) -> function
      | Ast.Module.SymbolDef (TypeDef def) ->
          (type_member path def :: types, operations, constants, nested)
      | SymbolDef (CallDef call)
        when Poly.equal call.call_decl.call_decl_kind Ast.Callable.Func ->
          (types, operation call :: operations, constants, nested)
      | SymbolDef (VarDef def) when def.var_decl.var_const ->
          ( types,
            operations,
            (name def.var_decl.var_name, typ def.var_decl.var_type) :: constants,
            nested )
      | SymbolDef (ModDef child) -> (types, operations, constants, child :: nested)
      | SymbolDef
          (ModInst _ | ConstrDef _ | DestrDef _ | FieldDef _ | VarDef _ | CallDef _)
      | Import _ ->
          (types, operations, constants, nested))
  in
  let parameters =
    List.map (Ast.Module.formals md.mod_decl) ~f:(fun formal ->
        { name = name formal.mod_inst_name; interface = qid_path formal.mod_inst_type })
  in
  let current =
    {
      path;
      interface = md.mod_decl.mod_decl_is_interface;
      parameters;
      implements = List.map (Set.to_list md.mod_decl.mod_decl_interfaces) ~f:qid_path;
      required_members = required_members md;
      types = List.rev types;
      operations = List.rev operations;
      constants = List.rev constants;
    }
  in
  current :: List.concat_map (List.rev nested) ~f:(modules path)

let standard_library () =
  Result.map (Raven_api.Library.standard_library ()) ~f:(fun library ->
      List.concat_map library.mod_def ~f:(function
        | Ast.Module.SymbolDef (Ast.Module.ModDef md) ->
            modules [ name library.mod_decl.mod_decl_name ] md
        | _ -> []))
