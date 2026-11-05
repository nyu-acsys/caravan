open Base

(* Saturn ocaml-multicore/saturn commit 50d8d9d0a99b40434ab05bee49200cd5ffa028f5,
   src/michael_scott_queue and src/treiber_stack.ml. Hashes cover original source bytes. *)
let sources =
  [
    ("michael_scott_queue.ml", "44f261d5d6d292d459bf2565a3373d02");
    ("michael_scott_queue.mli", "03b452397d50b26d0cd1395328ff3484");
    ("michael_scott_queue_intf.mli", "1ae5fc2cd8772b89f798abbcd6af52c4");
  ]

let strip_annotations text =
  let lexbuf = Lexing.from_string text in
  Lexer.init ();
  let rec lex () = match Lexer.token lexbuf with Parser.EOF -> () | _ -> lex () in
  lex ();
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
    List.filter_map (Lexer.comments ()) ~f:(fun (_, (loc : Location.t)) ->
        let start = loc.loc_start.pos_cnum and stop = loc.loc_end.pos_cnum in
        if not (String.is_prefix (String.drop_prefix text start) ~prefix:"(*@") then None
        else
          let first = line_start start and last = line_end stop in
          if whitespace first start && whitespace stop last then
            Some (first, if last < length then last + 1 else last)
          else Some (start, stop))
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

let () =
  List.iter sources ~f:(fun (name, expected) ->
      let path = "../saturn/michael_scott_queue/" ^ name in
      let source = Stdio.In_channel.read_all path in
      let source =
        if String.is_suffix name ~suffix:".ml" then source else strip_annotations source
      in
      let actual = Stdlib.Digest.(to_hex (string source)) in
      if not (String.equal expected actual) then
        failwith
          ("Upstream source parity failed for " ^ name ^ ": expected " ^ expected
         ^ ", got " ^ actual))

let () =
  let path = "../saturn/treiber_stack/treiber_stack.ml" in
  let source = Stdio.In_channel.read_all path in
  let expected = "4cb46bd94b98e275e25c9cffcc159cc9" in
  let actual = Stdlib.Digest.(to_hex (string source)) in
  if not (String.equal expected actual) then
    failwith
      ("Upstream source parity failed for treiber_stack.ml: expected " ^ expected
     ^ ", got " ^ actual)
