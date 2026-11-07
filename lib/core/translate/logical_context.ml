(** Source types of logical bindings whose state records are represented by fields. *)

open Base
open Translate_context

let variables env =
  let visible =
    List.dedup_and_sort (List.map env.vars ~f:fst) ~compare:String.compare
    |> List.map ~f:(fun name ->
        (name, List.Assoc.find_exn env.vars name ~equal:String.equal))
  in
  let projections =
    List.concat_map visible ~f:(fun (record, binding) ->
        match binding with
        | State fields ->
            List.map fields ~f:(fun (field, (_, typ)) ->
                (Source.record_field record field, typ))
        | Raven _ | Value _ -> [])
  in
  projections @ Source.shadow_record_projections (List.map visible ~f:fst) env.var_types
