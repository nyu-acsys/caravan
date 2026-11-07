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
