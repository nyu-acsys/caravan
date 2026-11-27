(** Callable effects checked at public contract boundaries. *)

open Base
module S = Caravan_spec.Spec_ast

let physically_atomic = function
  | None -> false
  | Some (contract : S.contract) ->
      Option.exists contract.header ~f:(fun header ->
          List.mem header.hd_name.pid_attrs "atomic" ~equal:String.equal)

let validate contract =
  match contract with
  | Some (contract : S.contract) when physically_atomic (Some contract) ->
      if
        contract.pure || contract.atomic
        || (not
              (List.is_empty contract.atomic_requires
              && List.is_empty contract.atomic_ensures
              && List.is_empty contract.atomic_raises))
        || Option.is_some contract.continues
      then
        let at =
          Option.value_map contract.header ~default:Location.none ~f:(fun header ->
              header.hd_name.pid_loc)
        in
        Error
          (Report.error Type at
             "A physically atomic contract cannot be pure or logically atomic")
      else Ok ()
  | _ -> Ok ()

let check ?(related = []) ~at ~expected ~actual () =
  let ( let* ) = Result.( >>= ) in
  let* () =
    Raw_contract.check ~related ~at
      ~expected:(Raw_contract.of_contract expected)
      ~actual:(Raw_contract.of_contract actual)
      ()
  in
  if physically_atomic expected && not (physically_atomic actual) then
    Error
      (Report.error ~related Type at
         "A physically atomic contract requires a physically atomic implementation")
  else Ok ()
