(** Rank-one function schemes and their source occurrence instantiations. *)

open Base

let ( let* ) result f = Result.bind result ~f

type scheme = { typ : Types.type_expr; variables : Types.type_expr list }
type restriction = { source : scheme; arguments : Types.type_expr list }

type witness = {
  parameter : int;  (** The position of the GADT witness among the parameters. *)
  interface : string;  (** The interface of the witness's implementations. *)
  members : int option list;
      (** Per variable, the witness's type parameter it is, whose dictionary it takes. *)
}
(** The witness of a function whose result types a GADT witness parameter selects. *)

type t = {
  id : Ident.t;
  paths : Path.t list;
  scheme : scheme;
  restriction : restriction option;
  witness : witness option;
  name : string;
  loc : Location.t;
}

let same_variable left right = Int.equal (Types.get_id left) (Types.get_id right)

let order_by workers ~name ~location ~dependencies =
  let rec place available emitted pending =
    let ready, pending =
      List.partition_tf pending ~f:(fun worker ->
          List.for_all (dependencies worker) ~f:(Set.mem available))
    in
    match (ready, pending) with
    | [], [] -> Ok (List.rev emitted)
    | [], worker :: _ ->
        Report.unsupported (location worker) "Cyclic generic declaration workers"
    | _ :: _, _ ->
        let available =
          List.fold ready ~init:available ~f:(fun available worker ->
              Set.add available (name worker))
        in
        place available (List.rev_append ready emitted) pending
  in
  place (Set.empty (module String)) [] workers

let order workers ~dependencies =
  order_by workers
    ~name:(fun worker -> worker.name)
    ~location:(fun worker -> worker.loc)
    ~dependencies

(** Includes nongeneric variables, so enclosing lexical binders can exclude them. *)
let all_variables typ =
  let rec visit (seen, variables) typ =
    let id = Types.get_id typ in
    if Set.mem seen id then (seen, variables)
    else
      let seen = Set.add seen id in
      match Types.get_desc typ with
      | Tvar _ | Tunivar _ -> (seen, typ :: variables)
      | _ -> Btype.fold_type_expr visit (seen, variables) typ
  in
  let _, variables = visit (Set.empty (module Int), []) typ in
  List.rev variables

let discover ?(excluded = []) ?(additional = []) ?(expand = Fn.id) ~at typ =
  let excluded = List.concat_map excluded ~f:all_variables in
  let unsupported () =
    Report.unsupported at "Higher-order or explicitly polymorphic function types"
  in
  let rec value (seen, variables) typ =
    let typ = expand typ in
    let id = Types.get_id typ in
    if Set.mem seen id then Ok (seen, variables)
    else
      let seen = Set.add seen id in
      match Types.get_desc typ with
      | Tvar _ ->
          let quantified =
            Types.get_level typ = Btype.generic_level
            && not (List.mem excluded typ ~equal:same_variable)
          in
          Ok (seen, if quantified then typ :: variables else variables)
      | Tunivar _ -> Ok (seen, typ :: variables)
      | Tconstr (_, arguments, _) ->
          List.fold_result arguments ~init:(seen, variables) ~f:value
      | Ttuple components ->
          List.fold_result components ~init:(seen, variables)
            ~f:(fun state (_, component) -> value state component)
      | Tpoly (body, []) -> value (seen, variables) body
      | Tarrow _ | Tpoly _ | Tobject _ | Tfield _ | Tnil | Tlink _ | Tsubst _ | Tvariant _
      | Tpackage _ | Tfunctor _ ->
          unsupported ()
  in
  let rec function_type state typ =
    let typ = expand typ in
    match Types.get_desc typ with
    | Tarrow (_, argument, result, _) ->
        let* state = value state argument in
        function_type state result
    | Tpoly (body, []) -> function_type state body
    (* An explicitly polymorphic function, as one with locally abstract types. *)
    | Tpoly (body, _ :: _) -> function_type state body
    | _ -> value state typ
  in
  let* state = function_type (Set.empty (module Int), []) typ in
  let* _, variables = List.fold_result additional ~init:state ~f:value in
  Ok { typ; variables = List.rev variables }

(** [typ] after [expand], without [Tpoly] wrappers: trivial ones, and those of explicitly
    polymorphic functions, whose universal variables are then the scheme's. *)
let rec monomorphic ~expand typ =
  let typ = expand typ in
  match Types.get_desc typ with Tpoly (body, _) -> monomorphic ~expand body | _ -> typ

(** Whether [left] and [right] are the same type, structurally after [expand]. *)
let same_type ?(expand = Fn.id) left right =
  let mono = monomorphic ~expand in
  let rec equal seen left right =
    let left = mono left and right = mono right in
    let pair = (Types.get_id left, Types.get_id right) in
    if Types.eq_type left right || List.mem seen pair ~equal:Poly.equal then true
    else
      let seen = pair :: seen in
      match (Types.get_desc left, Types.get_desc right) with
      | Tconstr (p, xs, _), Tconstr (q, ys, _) ->
          Path.same p q && List.equal (equal seen) xs ys
      | Ttuple xs, Ttuple ys ->
          List.equal (Option.equal String.equal) (List.map xs ~f:fst) (List.map ys ~f:fst)
          && List.equal (equal seen) (List.map xs ~f:snd) (List.map ys ~f:snd)
      | Tarrow (label, a, b, _), Tarrow (label', a', b', _) ->
          Poly.equal label label' && equal seen a a' && equal seen b b'
      | _ -> false
  in
  equal [] left right

let instantiate ?(expand = Fn.id) ~at scheme ~declaration ~occurrence =
  let mismatch () =
    Report.unsupported at "This polymorphic function occurrence or signature alias"
  in
  let mono = monomorphic ~expand in
  let equal = same_type ~expand in
  let* declared = discover ~expand ~at declaration in
  let* _ = discover ~expand ~at occurrence in
  let* native = discover ~expand ~at scheme.typ in
  let inferred =
    List.filter native.variables ~f:(fun variable ->
        List.mem scheme.variables variable ~equal:same_variable)
  in
  if List.length declared.variables <> List.length inferred then mismatch ()
  else
    let slot variables typ =
      List.findi variables ~f:(fun _ variable -> same_variable typ variable)
      |> Option.map ~f:fst
    in
    let rec aligned seen original declaration =
      let original = mono original and declaration = mono declaration in
      let pair = (Types.get_id original, Types.get_id declaration) in
      match slot inferred original with
      | Some index ->
          Option.equal Int.equal (Some index) (slot declared.variables declaration)
      | None -> (
          let contains_slot =
            List.exists (all_variables original) ~f:(fun variable ->
                Option.is_some (slot inferred variable))
          in
          if (not contains_slot) || List.mem seen pair ~equal:Poly.equal then true
          else
            let seen = pair :: seen in
            match (Types.get_desc original, Types.get_desc declaration) with
            | Tarrow (label, a, b, _), Tarrow (label', a', b', _) ->
                Poly.equal label label' && aligned seen a a' && aligned seen b b'
            | Ttuple xs, Ttuple ys ->
                List.equal (Option.equal String.equal) (List.map xs ~f:fst)
                  (List.map ys ~f:fst)
                && List.equal (aligned seen) (List.map xs ~f:snd) (List.map ys ~f:snd)
            | Tconstr (_, xs, _), Tconstr (_, ys, _) -> List.equal (aligned seen) xs ys
            | _ -> false)
    in
    if not (aligned [] scheme.typ declaration) then mismatch ()
    else
      let rec match_type seen bindings declaration occurrence =
        let source_occurrence = occurrence in
        let declaration = mono declaration and occurrence = mono occurrence in
        let pair = (Types.get_id declaration, Types.get_id occurrence) in
        match
          List.findi declared.variables ~f:(fun _ variable ->
              same_variable declaration variable)
        with
        | Some (slot, _) ->
            begin match List.Assoc.find bindings slot ~equal:Int.equal with
            | None -> Ok ((slot, source_occurrence) :: bindings)
            | Some previous when equal previous occurrence -> Ok bindings
            | Some _ -> mismatch ()
            end
        | None when List.mem seen pair ~equal:Poly.equal -> Ok bindings
        | None ->
            let seen = pair :: seen in
            begin match (Types.get_desc declaration, Types.get_desc occurrence) with
            | Tconstr (p, xs, _), Tconstr (q, ys, _) when Path.same p q ->
                match_list seen bindings xs ys
            | Ttuple xs, Ttuple ys
              when List.equal (Option.equal String.equal) (List.map xs ~f:fst)
                     (List.map ys ~f:fst) ->
                match_list seen bindings (List.map xs ~f:snd) (List.map ys ~f:snd)
            | Tarrow (label, a, b, _), Tarrow (label', a', b', _)
              when Poly.equal label label' ->
                let* bindings = match_type seen bindings a a' in
                match_type seen bindings b b'
            | _ when equal declaration occurrence -> Ok bindings
            | _ -> mismatch ()
            end
      and match_list seen bindings xs ys =
        match (xs, ys) with
        | [], [] -> Ok bindings
        | x :: xs, y :: ys ->
            let* bindings = match_type seen bindings x y in
            match_list seen bindings xs ys
        | [], _ :: _ | _ :: _, [] -> mismatch ()
      in
      let* bindings = match_type [] [] declaration occurrence in
      List.map scheme.variables ~f:(fun variable ->
          match slot inferred variable with
          | Some slot ->
              begin match List.Assoc.find bindings slot ~equal:Int.equal with
              | Some typ -> Ok typ
              | None -> mismatch ()
              end
          (* Lifted captures retain the lexical caller's dictionary. Their variables
             do not occur in the native arrow type matched above. *)
          | None -> Ok variable)
      |> Result.all

(** Continuation contracts may select an instance of an OCaml-generalized helper. Every
    occurrence must satisfy that instance before selecting its worker. *)
let instantiate_worker ?(expand = Fn.id) ~at worker ~declaration ~occurrence =
  match worker.restriction with
  | None -> instantiate ~expand ~at worker.scheme ~declaration ~occurrence
  | Some restriction ->
      let* arguments =
        instantiate ~expand ~at restriction.source ~declaration ~occurrence
      in
      let* substitute =
        Report.expect ~at "A type argument for each variable of the helper's instance"
          (Datatypes.substitution restriction.source.variables arguments)
      in
      let restricted = List.map restriction.arguments ~f:substitute in
      if not (List.equal (same_type ~expand) arguments restricted) then
        Error
          (Report.error Report.Type at
             "This call does not satisfy the helper's continuation type instance")
      else Ok (List.map worker.scheme.variables ~f:substitute)
