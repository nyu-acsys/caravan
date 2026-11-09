(** Native mutex operations, identified after compiler path normalization. *)

open Base

type t = Create | Lock | Unlock | Try_lock | Protect

let member path =
  match path with
  | Path.Pdot (Path.Pident root, name)
    when Ident.persistent root && String.equal (Ident.name root) "Stdlib__Mutex" ->
      Some name
  | Pdot (Pdot (Pident root, "Mutex"), name)
    when Ident.persistent root && String.equal (Ident.name root) "Stdlib" ->
      Some name
  | Pident _ | Pdot _ | Papply _ | Pextra_ty _ -> None

let is_type path = Option.equal String.equal (member path) (Some "t")
let is_module path = is_type (Path.Pdot (path, "t"))

let operation path =
  match member path with
  | Some "create" -> Some Create
  | Some "lock" -> Some Lock
  | Some "unlock" -> Some Unlock
  | Some "try_lock" -> Some Try_lock
  | Some "protect" -> Some Protect
  | Some _ | None -> None

let name = function
  | Create -> "create"
  | Lock -> "lock"
  | Unlock -> "unlock"
  | Try_lock -> "try_lock"
  | Protect -> "protect"
