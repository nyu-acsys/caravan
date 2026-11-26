(** Rewrites the includes of module expressions other than paths into those of paths:
    [include struct ... end] becomes its items, and an include of a functor application
    includes a module bound to it. *)

open Base

let hidden_prefix = "Caravan__include"

(** Whether [name] is that of a module bound for an include. *)
let is_hidden name = String.is_prefix name ~prefix:hidden_prefix

let hidden_name (location : Location.t) =
  Printf.sprintf "%s_%d_%d" hidden_prefix location.loc_start.pos_lnum
    (location.loc_start.pos_cnum - location.loc_start.pos_bol)

let rewrite_item (item : Parsetree.structure_item) =
  match item.pstr_desc with
  | Pstr_include { pincl_mod = { pmod_desc = Pmod_structure items; _ }; _ } -> items
  | Pstr_include
      ({ pincl_mod = { pmod_desc = Pmod_apply _ | Pmod_apply_unit _; _ } as applied; _ }
       as declaration) ->
      let loc = item.pstr_loc in
      let name = hidden_name loc in
      let binding =
        Ast_helper.Str.module_ ~loc
          (Ast_helper.Mb.mk ~loc (Location.mkloc (Some name) loc) applied)
      in
      let path = Ast_helper.Mod.ident ~loc (Location.mkloc (Longident.Lident name) loc) in
      [
        binding;
        { item with pstr_desc = Pstr_include { declaration with pincl_mod = path } };
      ]
  | _ -> [ item ]

let mapper =
  let structure self items =
    Ast_mapper.default_mapper.structure self items |> List.concat_map ~f:rewrite_item
  in
  { Ast_mapper.default_mapper with structure }

let rewrite structure = mapper.structure mapper structure
