(** Declaration lookup uses compiler identities, including every module component. *)

open Base

type 'a t = { entries : (Path.t * 'a) list }

let empty = { entries = [] }
let of_list entries = { entries }
let add bindings path value = { entries = (path, value) :: bindings.entries }
let find bindings path = List.Assoc.find bindings.entries path ~equal:Path.same
let mem bindings path = Option.is_some (find bindings path)

let member bindings = function
  | Path.Pdot (parent, name) ->
      Option.map (find bindings parent) ~f:(fun path -> Qualified_name.{ path; name })
  | Pident _ | Papply _ | Pextra_ty _ -> None
