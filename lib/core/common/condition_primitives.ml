(** Native condition operations, identified after compiler path normalization. *)

open Base

type t = Create | Wait | Signal | Broadcast

let member path =
  match path with
  | Path.Pdot (Path.Pident root, name)
    when Ident.persistent root && String.equal (Ident.name root) "Stdlib__Condition" ->
      Some name
  | Pdot (Pdot (Pident root, "Condition"), name)
    when Ident.persistent root && String.equal (Ident.name root) "Stdlib" ->
      Some name
  | Pident _ | Pdot _ | Papply _ | Pextra_ty _ -> None

let is_type path = Option.equal String.equal (member path) (Some "t")
let is_module path = is_type (Path.Pdot (path, "t"))

let operation path =
  match member path with
  | Some "create" -> Some Create
  | Some "wait" -> Some Wait
  | Some "signal" -> Some Signal
  | Some "broadcast" -> Some Broadcast
  | Some _ | None -> None
