(* The declarations of [list_segment s over p]: the iteration [s_seg] of an element
   predicate [p] over a list, the list with a hole at one index, [s_hole], and the lemmas
   that take an element out of the list and put it back, [s_expose] and [s_restore]. *)

open Spec_ast

let rec same_qualid a b =
  match (a, b) with
  | Qid a, Qid b -> String.equal a.pid_str b.pid_str
  | Qdot (qa, a), Qdot (qb, b) -> String.equal a.pid_str b.pid_str && same_qualid qa qb
  | _ -> false

(** Whether [a] and [b] are the same type, wherever they are written. *)
let rec same_type a b =
  match (a, b) with
  | PTtyany, PTtyany -> true
  | PTtyvar a, PTtyvar b -> String.equal a.pid_str b.pid_str
  | PTtyapp (qa, xs), PTtyapp (qb, ys) -> same_qualid qa qb && List.equal same_type xs ys
  | PTtuple xs, PTtuple ys -> List.equal same_type xs ys
  | PTarrow (a1, a2), PTarrow (b1, b2) -> same_type a1 b1 && same_type a2 b2
  | _ -> false

(** The declarations of [list_segment name over element], at [loc]; [element] is
    [predicate p (position : integer) (x : t) (tail : t list) (q : u) ...]. *)
let declarations ~loc ~(name : id) (element : predicate) : proof_decl list =
  let id ?(fixity = Normal) s = mk_id ~fixity ~loc s in
  let term d = mk_term d loc in
  let var s = term (Tvar (Qid (id s))) in
  let apply f args = term (mk_op_apply (id f) args) in
  let infix op l r = term (mk_op_apply (id ~fixity:Infix op) [ l; r ]) in
  let pat d = { pat_desc = d; pat_loc = loc } in
  let tyapp s args = PTtyapp (Qid (id s), args) in
  let element_type, extras =
    match element.pred_params with
    | (_, PTtyapp (Qid { pid_str = "integer"; _ }, [])) :: (_, x) :: (_, tail) :: extras
      ->
        begin match tail with
        | PTtyapp (Qid { pid_str = "list"; _ }, [ t ]) when same_type t x -> (x, extras)
        | _ ->
            raise
              (Syntax_error
                 ( loc,
                   "The third parameter of a list segment's element predicate must be \
                    the list after the element, a list of the element's type" ))
        end
    | _ ->
        raise
          (Syntax_error
             ( loc,
               "A list segment's element predicate must take the position, as an \
                integer, the element and the list after it, then its own parameters" ))
  in
  let taken = List.map (fun (x, _) -> x.pid_str) extras in
  let rec fresh base = if List.mem base taken then fresh (base ^ "_") else base in
  let nodes = fresh "nodes"
  and position = fresh "position"
  and index = fresh "index"
  and target = fresh "target"
  and first = fresh "first"
  and rest = fresh "rest" in
  let extra_args = List.map (fun (x, _) -> var x.pid_str) extras in
  let extra_params = List.map (fun (x, t) -> (id x.pid_str, t)) extras in
  let list_type = tyapp "list" [ element_type ] in
  let integer = tyapp "integer" [] in
  let named suffix = name.pid_str ^ "_" ^ suffix in
  let seg_name = named "seg"
  and hole_name = named "hole"
  and located_name = named "located"
  and suffix_name = named "suffix"
  and expose_name = named "expose"
  and restore_name = named "restore" in
  let next_position =
    infix "+" (var position) (term (Tconst (Pconst_integer ("1", None))))
  in
  let at_index = infix "=" (var position) (var index) in
  let seg args = apply seg_name args in
  let hole args = apply hole_name args in
  let phi args = apply element.pred_name.pid_str args in
  let cases nil cons =
    [
      (pat (Pconstr (Qid (id "[]"), None)), nil);
      ( pat
          (Pconstr
             ( Qid (id ~fixity:Infix "::"),
               Some (pat (Ptuple [ pat (Pid (id first)); pat (Pid (id rest)) ])) )),
        cons );
    ]
  in
  let on_nodes nil cons = term (Tmatch (var nodes, cases nil cons)) in
  let element_holds = phi ([ var position; var first; var rest ] @ extra_args) in
  let seg_of_rest = seg ([ var rest; next_position ] @ extra_args) in
  let predicate pred_name params body =
    Proof_predicate
      {
        pred_name = id pred_name;
        pred_params = params;
        pred_body = Some body;
        pred_persistent = false;
        pred_inline = false;
      }
  in
  let seg_decl =
    predicate seg_name
      ([ (id nodes, list_type); (id position, integer) ] @ extra_params)
      (on_nodes (term Ttrue) (infix "&&" element_holds seg_of_rest))
  in
  let hole_decl =
    predicate hole_name
      ([ (id nodes, list_type); (id position, integer) ]
      @ extra_params
      @ [ (id index, integer) ])
      (on_nodes (term Tfalse)
         (term
            (Tif
               ( at_index,
                 seg_of_rest,
                 infix "&&" element_holds
                   (hole ([ var rest; next_position ] @ extra_args @ [ var index ])) ))))
  in
  let function_ function_name params result body =
    Proof_function
      {
        function_name = id function_name;
        function_params = params;
        function_result = result;
        function_recursive = true;
        function_variant = [ var nodes ];
        function_body = body;
      }
  in
  let located_decl =
    function_ located_name
      [
        (id nodes, list_type);
        (id position, integer);
        (id index, integer);
        (id target, element_type);
      ]
      (tyapp "bool" [])
      (on_nodes (term Tfalse)
         (term
            (Tif
               ( at_index,
                 infix "===" (var first) (var target),
                 apply located_name [ var rest; next_position; var index; var target ] ))))
  in
  let suffix_decl =
    function_ suffix_name
      [ (id nodes, list_type); (id position, integer); (id index, integer) ]
      list_type
      (on_nodes (var "[]")
         (term
            (Tif
               ( at_index,
                 var rest,
                 apply suffix_name [ var rest; next_position; var index ] ))))
  in
  let lemma_params =
    [ (id nodes, list_type); (id position, integer) ]
    @ extra_params
    @ [ (id index, integer); (id target, element_type) ]
  in
  let lemma_rest_args =
    [ var rest; next_position ] @ extra_args @ [ var index; var target ]
  in
  let whole = seg ([ var nodes; var position ] @ extra_args) in
  let holed = hole ([ var nodes; var position ] @ extra_args @ [ var index ]) in
  let located = apply located_name [ var nodes; var position; var index; var target ] in
  let exposed =
    phi
      ([ var index; var target; apply suffix_name [ var nodes; var position; var index ] ]
      @ extra_args)
  in
  let proof d = { proof_desc = d; proof_loc = loc } in
  let seq a b = proof (Proof_seq (a, b)) in
  let fold t = proof (Proof_fold (t, [])) in
  let unfold t = proof (Proof_unfold (t, [])) in
  let call lemma args = proof (Proof_value (apply lemma args)) in
  let on_nodes_proof nil cons = proof (Proof_match (var nodes, cases nil cons)) in
  let lemma lemma_name requires ensures body =
    Proof_lemma
      {
        lemma_name = id lemma_name;
        lemma_params;
        lemma_returns = [];
        lemma_requires = requires;
        lemma_ensures = ensures;
        lemma_variant = [ var nodes ];
        lemma_opens = Some (loc, []);
        lemma_body = body;
      }
  in
  let expose_decl =
    lemma expose_name
      [ infix "&&" whole located ]
      [ infix "&&" holed exposed ]
      (on_nodes_proof
         (proof (Proof_assert (term Tfalse)))
         (seq (unfold whole)
            (proof
               (Proof_if
                  ( at_index,
                    fold holed,
                    seq (call expose_name lemma_rest_args) (fold holed) )))))
  in
  let restore_decl =
    lemma restore_name
      [ infix "&&" (infix "&&" holed located) exposed ]
      [ whole ]
      (on_nodes_proof (unfold holed)
         (seq (unfold holed)
            (proof
               (Proof_if
                  ( at_index,
                    fold whole,
                    seq (call restore_name lemma_rest_args) (fold whole) )))))
  in
  [ seg_decl; hole_decl; located_decl; suffix_decl; expose_decl; restore_decl ]
