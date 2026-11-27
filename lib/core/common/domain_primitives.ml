(** Standard-library domain operations, identified after compiler path normalization. *)

open Base

type t = Spawn | Join

let operation path =
  let member = function "spawn" -> Some Spawn | "join" -> Some Join | _ -> None in
  match path with
  | Path.Pdot (Path.Pident root, name)
    when Ident.persistent root && String.equal (Ident.name root) "Stdlib__Domain" ->
      member name
  | Pdot (Pdot (Pident root, "Domain"), name)
    when Ident.persistent root && String.equal (Ident.name root) "Stdlib" ->
      member name
  | Pident _ | Pdot _ | Papply _ | Pextra_ty _ -> None
