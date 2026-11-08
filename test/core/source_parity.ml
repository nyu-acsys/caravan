open Base

(* Saturn ocaml-multicore/saturn commit 50d8d9d0a99b40434ab05bee49200cd5ffa028f5,
   src/michael_scott_queue and src/treiber_stack. Hashes cover original source bytes. *)
let sources =
  [
    ("michael_scott_queue/michael_scott_queue.ml", "44f261d5d6d292d459bf2565a3373d02");
    ("michael_scott_queue/michael_scott_queue.mli", "03b452397d50b26d0cd1395328ff3484");
    ( "michael_scott_queue/michael_scott_queue_intf.mli",
      "1ae5fc2cd8772b89f798abbcd6af52c4" );
    ( "michael_scott_queue_lseg/michael_scott_queue_lseg.ml",
      "44f261d5d6d292d459bf2565a3373d02" );
    ( "michael_scott_queue_lseg/michael_scott_queue_lseg.mli",
      "03b452397d50b26d0cd1395328ff3484" );
    ( "michael_scott_queue_lseg/michael_scott_queue_lseg_intf.mli",
      "1ae5fc2cd8772b89f798abbcd6af52c4" );
    ("treiber_stack/treiber_stack.ml", "4cb46bd94b98e275e25c9cffcc159cc9");
    ("treiber_stack/treiber_stack.mli", "8fce1984f67b2eb286143e8ebf3ea2fd");
  ]

let strip_annotations text =
  let lexbuf = Lexing.from_string text in
  Lexer.init ();
  let signature = Parse.interface lexbuf in
  let annotations =
    List.filter_map (Lexer.comments ()) ~f:(fun (_, (loc : Location.t)) ->
        Option.some_if
          (String.is_prefix
             (String.drop_prefix text loc.loc_start.pos_cnum)
             ~prefix:"(*@")
          loc)
  in
  let attributes = ref [] in
  let attribute iterator (attribute : Parsetree.attribute) =
    if String.is_prefix attribute.attr_name.txt ~prefix:"caravan." then
      attributes := attribute.attr_loc :: !attributes
    else Ast_iterator.default_iterator.attribute iterator attribute
  in
  let iterator = { Ast_iterator.default_iterator with attribute } in
  iterator.signature iterator signature;
  let length = String.length text in
  let rec line_start offset =
    if offset = 0 || Char.equal text.[offset - 1] '\n' then offset
    else line_start (offset - 1)
  in
  let rec line_end offset =
    if offset = length || Char.equal text.[offset] '\n' then offset
    else line_end (offset + 1)
  in
  let whitespace start stop =
    String.for_all
      (String.sub text ~pos:start ~len:(stop - start))
      ~f:(function ' ' | '\t' -> true | _ -> false)
  in
  let ranges =
    List.map (annotations @ !attributes) ~f:(fun (loc : Location.t) ->
        let start = loc.loc_start.pos_cnum and stop = loc.loc_end.pos_cnum in
        let first = line_start start and last = line_end stop in
        if whitespace first start && whitespace stop last then
          (first, if last < length then last + 1 else last)
        else (start, stop))
    |> List.sort ~compare:(fun (left, _) (right, _) -> Int.compare left right)
  in
  let buffer = Buffer.create length in
  let final =
    List.fold ranges ~init:0 ~f:(fun offset (start, stop) ->
        Buffer.add_substring buffer text ~pos:offset ~len:(start - offset);
        stop)
  in
  Buffer.add_substring buffer text ~pos:final ~len:(length - final);
  Buffer.contents buffer

let normalize_module_name name source =
  if String.equal name "michael_scott_queue_lseg/michael_scott_queue_lseg.mli" then
    let suffix = "include Michael_scott_queue_lseg_intf.MS_QUEUE\n" in
    match String.chop_suffix source ~suffix with
    | Some prefix -> prefix ^ "include Michael_scott_queue_intf.MS_QUEUE\n"
    | None -> source
  else source

let check_digest name expected source =
  let actual = Stdlib.Digest.(to_hex (string source)) in
  if not (String.equal expected actual) then
    failwith
      ("Upstream source parity failed for " ^ name ^ ": expected " ^ expected ^ ", got "
     ^ actual)

(* The barrier-free tutorial functor, with integer IDs and a named loop counter. *)
let stack_drain_body source =
  let after marker source =
    match String.substr_index source ~pattern:marker with
    | Some index -> String.drop_prefix source (index + String.length marker)
    | None -> failwith ("Missing stack-drain source marker " ^ marker)
  in
  let body = after "module Test (Stack : S) = struct\n" source in
  let body =
    match String.substr_index body ~pattern:"\nend\n" with
    | Some index -> String.prefix body index
    | None -> failwith "Missing stack-drain functor end"
  in
  List.fold
    [
      ("(id : int)", "(id : string)");
      ("for i = 0 to 9 do", "for _ = 0 to 9 do");
      ("work 1 st", "work \"A\" st");
      ("work 2 st", "work \"B\" st");
    ]
    ~init:body
    ~f:(fun body (pattern, with_) -> String.substr_replace_all body ~pattern ~with_)

let () =
  List.iter sources ~f:(fun (name, expected) ->
      let path = "../saturn/" ^ name in
      let source = Stdio.In_channel.read_all path in
      let source =
        if String.is_suffix name ~suffix:".ml" then source else strip_annotations source
      in
      let source = normalize_module_name name source in
      check_digest name expected source);
  check_digest "stack_drain/stack_drain.ml (tutorial functor)"
    "eb5cb2cf56e88545ebc55dc986cf436a"
    (stack_drain_body (Stdio.In_channel.read_all "../saturn/stack_drain/stack_drain.ml"))
