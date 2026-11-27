(** Raw carriers are an explicit part of ordinary callable contracts. *)

open Base
module S = Caravan_spec.Spec_ast

type t = { arguments : bool list; result : bool }

let marked (id : S.id) = List.mem id.pid_attrs "raw" ~equal:String.equal

let of_header = function
  | None -> { arguments = []; result = false }
  | Some (header : S.header) ->
      {
        arguments =
          List.filter_map header.hd_args ~f:(function
            | S.Lvar id -> Some (marked id)
            | Lunit _ | Lwild -> Some false
            | Lghost _ -> None);
        result =
          List.exists header.hd_ret ~f:(function
            | S.Lvar id -> marked id
            | Lunit _ | Lwild | Lghost _ -> false);
      }

let of_contract contract = of_header (Option.bind contract ~f:(fun c -> c.S.header))
let any modes = modes.result || List.exists modes.arguments ~f:Fn.id
let argument modes index = Option.value (List.nth modes.arguments index) ~default:false

let check ?(related = []) ~at ~expected ~actual () =
  let count = Int.max (List.length expected.arguments) (List.length actual.arguments) in
  let mismatch =
    List.find (List.init count ~f:Fn.id) ~f:(fun index ->
        not (Bool.equal (argument expected index) (argument actual index)))
  in
  let error message = Error (Report.error ~related Type at message) in
  match mismatch with
  | Some index ->
      error
        (Printf.sprintf
           "Argument %d has different raw modes in the interface and implementation"
           (index + 1))
  | None when not (Bool.equal expected.result actual.result) ->
      error "The result has different raw modes in the interface and implementation"
  | None -> Ok ()
