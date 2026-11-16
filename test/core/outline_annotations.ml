open Base
module C = Caravan_core

let get = function
  | Ok value -> value
  | Error (error : C.Report.error) -> failwith error.message

let lexbuf file text =
  let buffer = Lexing.from_string text in
  Location.init buffer file;
  buffer

let source =
  "module Box = struct\n\
   let read c = Atomic.get c\n\
   end\n\
   let outer c =\n\
   let inner d = Atomic.get d in\n\
   let a = (* 🙂 *) Atomic.get c in\n\
   inner c + a\n"

let proof =
  "module Box = struct\n\
   proof read = at (Atomic.get c) commit\n\
   end\n\
   proof outer =\n\
   proof inner = begin at (Atomic.get d) commit end;\n\
   at (let a = Atomic.get c) (fun step -> step ());\n\
   on return assert ((* 🙂 *) true)\n"

let slice text (location : Location.t) =
  String.sub text ~pos:location.loc_start.pos_cnum
    ~len:(location.loc_end.pos_cnum - location.loc_start.pos_cnum)

let endpoint pattern = String.substr_index_exn source ~pattern + String.length pattern

let () =
  let structure = Parse.implementation (lexbuf "outline.ml" source) in
  let parsed =
    Caravan_spec.Spec_parser.proof Caravan_spec.Spec_lexer.token
      (lexbuf "outline.proof" proof)
  in
  let annotations =
    get (C.Outline.annotations ~proof_text:proof ~structure ~annotations:[] parsed)
  in
  let steps =
    List.filter_map annotations ~f:(fun (annotation : C.Annotation.t) ->
        Option.map annotation.origin ~f:(fun origin -> (annotation, origin)))
  in
  let expected =
    [
      ("commit", "", "let read c = Atomic.get c");
      ("(fun step -> step ())", "Ghost.scope ", "let a = (* 🙂 *) Atomic.get c");
      ("assert ((* 🙂 *) true)", "proof ", "inner c + a");
      ("commit", "", "let inner d = Atomic.get d");
    ]
  in
  assert (List.length steps = List.length expected);
  List.iter expected ~f:(fun (text, prefix, anchor) ->
      let annotation, origin =
        List.find_exn steps ~f:(fun (annotation, _) ->
            annotation.C.Annotation.loc.loc_start.pos_cnum = endpoint anchor)
      in
      assert (String.equal (slice proof origin.loc) text);
      assert (String.equal annotation.text (prefix ^ text));
      assert (String.equal origin.loc.loc_start.pos_fname "outline.proof");
      assert (
        origin.position.pos_cnum = origin.loc.loc_start.pos_cnum - String.length prefix);
      assert (Poly.equal (C.Annotation.lexbuf annotation).lex_curr_p origin.position);
      assert (String.equal annotation.loc.loc_start.pos_fname "outline.ml");
      assert (annotation.loc.loc_start.pos_cnum = endpoint anchor);
      assert (Poly.equal annotation.loc.loc_start annotation.loc.loc_end));
  let generated =
    List.filter annotations ~f:(fun a -> Option.is_none a.C.Annotation.origin)
  in
  assert (List.length generated = 1);
  assert (List.for_all generated ~f:(fun a -> String.equal a.text "manual"));
  List.iter steps ~f:(fun (annotation, _) ->
      match C.Annotation.kind annotation with
      | Scope -> ignore (get (C.Annotation.scope annotation))
      | Proof -> ignore (get (C.Annotation.proof annotation))
      | Linearization -> ignore (get (C.Annotation.linearization annotation))
      | Contract | Loop | Predicate | Ghost_module | Ghost | Returns | Manual | Initially
      | Initializes | Trusted ->
          failwith "Expected an outline proof step")

let () =
  let source = "let identity (value : int) = value\n" in
  let proof =
    "proof result, [copy : int] = identity value\n\
     ensures (result === value && copy === value) =\n\
     on return Ghost.returns (fun result () -> result)\n"
  in
  let structure = Parse.implementation (lexbuf "adapter.ml" source) in
  let parsed =
    Caravan_spec.Spec_parser.proof Caravan_spec.Spec_lexer.token
      (lexbuf "adapter.proof" proof)
  in
  let annotations =
    get (C.Outline.annotations ~proof_text:proof ~structure ~annotations:[] parsed)
  in
  let adapter =
    List.find_exn annotations ~f:(fun annotation ->
        match C.Annotation.kind annotation with Returns -> true | _ -> false)
  in
  ignore (get (C.Annotation.returns adapter));
  let origin = Option.value_exn adapter.origin in
  assert (String.equal adapter.text (slice proof origin.loc));
  assert (String.equal origin.loc.loc_start.pos_fname "adapter.proof");
  let contract =
    List.find_exn annotations ~f:(fun annotation ->
        match C.Annotation.kind annotation with Contract -> true | _ -> false)
  in
  ignore (get (C.Annotation.contract contract))

let () =
  let proof =
    "proof read =\n\
     let known = at (let first = Atomic.get cell) (fun step ->\n\
     let result = step () in (result, result)) in\n\
     at (let second = Atomic.get cell) (fun step ->\n\
     let result = step () in assert (result = known); result)\n"
  in
  let annotations source =
    let structure = Parse.implementation (lexbuf "nested.ml" source) in
    let parsed =
      Caravan_spec.Spec_parser.proof Caravan_spec.Spec_lexer.token
        (lexbuf "nested.proof" proof)
    in
    C.Outline.annotations ~proof_text:proof ~structure ~annotations:[] parsed
  in
  let nested =
    "let read cell outer inner =\n\
     if outer then\n\
     let first = Atomic.get cell in\n\
     if inner then let second = Atomic.get cell in second else first\n\
     else 0\n"
  in
  let nested_annotations = get (annotations nested) in
  let imports =
    List.concat_map nested_annotations ~f:(fun annotation ->
        Option.value_map annotation.C.Annotation.outline ~default:[] ~f:(fun outline ->
            outline.imports))
  in
  begin match imports with
  | [ (_, pattern) ] ->
      assert (
        List.equal String.equal (Caravan_spec.Spec_ast.pat_names pattern) [ "known" ])
  | _ -> failwith "A nested branch must import its enclosing branch's export"
  end;
  let siblings =
    "let read cell outer inner =\n\
     if outer then\n\
     if inner then let first = Atomic.get cell in first\n\
     else let second = Atomic.get cell in second\n\
     else 0\n"
  in
  match annotations siblings with
  | Error error ->
      assert (String.is_substring error.message ~substring:"does not run on every path")
  | Ok _ -> failwith "An export cannot cross sibling branches"

let () =
  let source = "let twice cell = Atomic.get cell + Atomic.get cell\n" in
  let structure = Parse.implementation (lexbuf "twice.ml" source) in
  let annotations selector =
    let proof =
      "proof twice = at ((Atomic.get cell)[@occurrence " ^ selector ^ "]) commit\n"
    in
    let parsed =
      Caravan_spec.Spec_parser.proof Caravan_spec.Spec_lexer.token
        (lexbuf "twice.proof" proof)
    in
    C.Outline.annotations ~proof_text:proof ~structure ~annotations:[] parsed
  in
  List.iter [ 1; 2 ] ~f:(fun occurrence ->
      let annotations = get (annotations (Int.to_string occurrence)) in
      let step =
        List.find_exn annotations ~f:(fun annotation ->
            Option.is_some annotation.C.Annotation.origin)
      in
      let first = String.substr_index_exn source ~pattern:"Atomic.get cell" in
      let expected =
        if occurrence = 1 then first
        else String.substr_index_exn ~pos:(first + 1) source ~pattern:"Atomic.get cell"
      in
      assert (step.loc.loc_start.pos_cnum = expected + String.length "Atomic.get cell"));
  List.iter [ "0"; "3"; "true" ] ~f:(fun selector ->
      assert (Result.is_error (annotations selector)))

let () =
  let call =
    "List.fold_left (fun (cell, count) value -> Atomic.set cell value; (cell, count)) \
     (cell, 0) values"
  in
  let source = "let reset cell values = " ^ call in
  let proof =
    "proof reset = at (" ^ call
    ^ ") invariant (fun (cell, count) remaining -> own cell value); at (Atomic.set cell \
       value) (fun step -> step ())"
  in
  let structure = Parse.implementation (lexbuf "fold.ml" source) in
  let parsed =
    Caravan_spec.Spec_parser.proof Caravan_spec.Spec_lexer.token
      (lexbuf "fold.proof" proof)
  in
  let annotations =
    get (C.Outline.annotations ~proof_text:proof ~structure ~annotations:[] parsed)
  in
  let loop =
    List.find_exn annotations ~f:(fun annotation ->
        Poly.equal (C.Annotation.kind annotation) C.Annotation.Loop)
  in
  let spec = get (C.Annotation.loop_spec loop) in
  assert (List.length (fst (List.hd_exn spec.state_invariants)) = 2);
  let target = Option.bind loop.outline ~f:(fun outline -> outline.target) in
  assert (String.equal (slice source (Option.value_exn target)) call);
  assert (
    loop.loc.loc_start.pos_cnum
    = String.substr_index_exn source ~pattern:"Atomic.set cell value")
