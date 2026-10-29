(** Source spellings, separate from compiler declaration identities. *)

open Base
module S = Caravan_spec.Spec_ast

type t = { path : string list; name : string }

let of_spec = function
  | S.Qid id -> { path = []; name = id.pid_str }
  | Qdot (parent, id) ->
      let rec components rest = function
        | S.Qid id -> id.pid_str :: rest
        | Qdot (parent, id) -> components (id.pid_str :: rest) parent
      in
      { path = components [] parent; name = id.pid_str }

let of_string text =
  match List.rev (String.split text ~on:'.') with
  | name :: reversed -> { path = List.rev reversed; name }
  | [] -> { path = []; name = text }

let to_string { path; name } = String.concat ~sep:"." (path @ [ name ])
let raven ~loc { path; name } = Raven_api.Name.make ~loc ~path name
