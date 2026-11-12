(** Checked transport of owner-indexed primitives across a visibility handoff. *)

open Base
open Translate_context

let executing = function
  | S.{ term_desc = Tvar (Qdot (Qid ghost, self)); _ } ->
      String.equal ghost.pid_str "Ghost" && String.equal self.pid_str "self"
  | _ -> false

let mobile env term =
  match spine term [] with
  | { term_desc = Tvar q; _ }, owner :: rest when executing owner ->
      Option.bind (access_method env q) ~f:(fun (field, method_) ->
          Option.some_if (String.equal method_ "visible") (field, q, rest))
  | _ -> None

let rec map_resources env ~primitive ~other (term : S.term) : S.term =
  match mobile env term with
  | Some resource -> primitive term resource
  | None ->
      let recurse = map_resources env ~primitive ~other in
      let desc =
        match term.S.term_desc with
        | Tinfix _ -> (recurse (S.chain term)).term_desc
        | Tif (condition, left, right) -> Tif (condition, recurse left, recurse right)
        | Tmatch (value, cases) ->
            Tmatch
              (value, List.map cases ~f:(fun (pattern, body) -> (pattern, recurse body)))
        | Tattr (attribute, body) -> Tattr (attribute, recurse body)
        | Tcast (body, typ) -> Tcast (recurse body, typ)
        | _ ->
            begin match spine term [] with
            | { term_desc = Tvar (Qid op); _ }, [ left; right ]
              when List.mem [ "&&"; "/\\" ] op.pid_str ~equal:String.equal ->
                S.mk_op_apply op [ recurse left; recurse right ]
            | { term_desc = Tvar (Qid op); _ }, [ condition; body ]
              when String.equal op.pid_str "->" ->
                S.mk_op_apply op [ condition; recurse body ]
            | _ -> other term
            end
      in
      { term with term_desc = desc }

let reindex env receiver =
  let primitive term (_, q, rest) =
    List.fold (receiver :: rest)
      ~init:S.{ term with term_desc = Tvar q }
      ~f:(fun fn arg -> S.{ term with term_desc = Tapply (fn, arg) })
  in
  map_resources env ~primitive ~other:(fun term -> term.term_desc)

let reindexed env ~receiver terms =
  let open State.Syntax in
  let at = match terms with [] -> Location.none | term :: _ -> term.S.term_loc in
  let* typ = State.of_result (Source.ghost_type env.ctx.given.env ~at) in
  let* source = State.fresh "transfer_receiver" in
  let env =
    { (bind env source (Value receiver)) with var_types = (source, typ) :: env.var_types }
  in
  let receiver = S.mk_term (Tvar (Qid (S.mk_id ~loc:at source))) at in
  State.return (env, List.map terms ~f:(reindex env receiver))

let formulas env ~receiver terms =
  let open State.Syntax in
  let* env, terms = reindexed env ~receiver terms in
  State.all terms ~f:(Spec_terms.formula env)

let rec steps env ~source ~target term =
  let open State.Syntax in
  let l = loc term.S.term_loc in
  match mobile env term with
  | Some (field, method_, owner :: arguments) ->
      let* signature =
        State.of_result
          (Spec_terms.equality_term_type env S.{ term with term_desc = Tvar method_ })
      in
      let inputs, _ = Proof_types.function_arguments signature in
      let* () =
        if List.length inputs = List.length arguments + 2 then State.return ()
        else State.of_result (error term.term_loc "Incorrect visible field arguments")
      in
      let* family, receiver, selected = Spec_terms.field_selection env field term owner in
      let+ arguments = State.all arguments ~f:(Spec_terms.formula env) in
      [
        R.Stmt.call ~loc:l
          (R.Expr.call ~loc:l
             (qualified_name ~loc:l (family ^ ".transfer"))
             (source :: target :: receiver :: selected :: arguments));
      ]
  | Some _ -> State.of_result (error term.term_loc "A visible field needs a cell")
  | None ->
      let recurse = steps env ~source ~target in
      begin match term.term_desc with
      | Tinfix _ -> recurse (S.chain term)
      | Tattr (_, body) | Tcast (body, _) -> recurse body
      | Tif (condition, left, right) ->
          let* condition = Spec_terms.formula env condition in
          let* left = recurse left in
          let+ right = recurse right in
          [ R.Stmt.if_ ~loc:l condition left right ]
      | Tmatch (value, cases) ->
          let* translated = Spec_terms.formula env value in
          let* typ = State.of_result (Spec_terms.equality_term_type env value) in
          let rec visit = function
            | [] -> State.return []
            | (pattern, body) :: rest ->
                let* condition, bindings =
                  State.of_result (Spec_terms.spec_pattern env pattern translated)
                in
                let case_env =
                  Spec_terms.spec_case_env env ~scrutinee:value ~scrutinee_type:typ
                    pattern
                in
                let case_env =
                  List.fold bindings ~init:case_env ~f:(fun env (name, value) ->
                      bind env name (Value value))
                in
                let* body = steps case_env ~source ~target body in
                begin match condition with
                | None -> State.return body
                | Some condition ->
                    let+ rest = visit rest in
                    [ R.Stmt.if_ ~loc:l condition body rest ]
                end
          in
          visit cases
      | _ ->
          begin match spine term [] with
          | { term_desc = Tvar (Qid op); _ }, [ left; right ]
            when List.mem [ "&&"; "/\\" ] op.pid_str ~equal:String.equal ->
              let* left = recurse left in
              let+ right = recurse right in
              left @ right
          | { term_desc = Tvar (Qid op); _ }, [ condition; body ]
            when String.equal op.pid_str "->" ->
              let* condition = Spec_terms.formula env condition in
              let+ body = recurse body in
              [ R.Stmt.if_ ~loc:l condition body [] ]
          | _ -> State.return []
          end
      end

let transfer env ~source ~target terms =
  let open State.Syntax in
  let+ statements = State.all terms ~f:(steps env ~source ~target) in
  List.concat statements

let retained env =
  map_resources env ~primitive:(fun term _ -> term) ~other:(fun _ -> S.Ttrue)

let retained_formulas env ~receiver terms =
  let terms =
    List.filter_map terms ~f:(fun term ->
        let term = retained env term in
        match term.S.term_desc with Ttrue -> None | _ -> Some term)
  in
  formulas env ~receiver terms
