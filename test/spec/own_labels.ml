open Caravan_spec
open Spec_ast

let term source = Spec_parser.term_eof Spec_lexer.token (Lexing.from_string source)

let proof source =
  match
    (Spec_parser.proof_expr_eof Spec_lexer.token (Lexing.from_string source)).proof_desc
  with
  | Proof_value term -> term
  | _ -> failwith "Expected a value proof expression"

let rec application term =
  match term.term_desc with
  | Tapply (fn, arg) ->
      let head, args = application fn in
      (head, args @ [ arg ])
  | _ -> (term, [])

let rec name = function
  | { term_desc = Tvar (Qid id); _ } -> id.pid_str
  | { term_desc = Tvar (Qdot (path, id)); _ } -> name_path path ^ "." ^ id.pid_str
  | _ -> ""

and name_path = function
  | Qid id -> id.pid_str
  | Qdot (path, id) -> name_path path ^ "." ^ id.pid_str

let check parse source expected =
  let head, args = application (parse source) in
  assert (name head = "own");
  assert (List.map name args = expected)

let check_release parse source fraction release =
  let head, args = application (parse source) in
  assert (name head = "own");
  match args with
  | [
   _location;
   _value;
   { term_desc = Tvar (Qdot (_, fraction_id)); _ };
   { term_desc = Ttuple []; _ };
   release_term;
  ] ->
      assert (fraction_id.pid_str = fraction);
      assert (name release_term = release)
  | _ -> failwith "Expected own release arguments"

let rejected parse source message =
  match parse source with
  | _ -> failwith ("Accepted " ^ source)
  | exception Syntax_error (_, actual) -> assert (actual = message)

let () =
  check term "own location value" [ "location"; "value" ];
  check term "own ~fraction:Permission.half location value"
    [ "location"; "value"; "Permission.half" ];
  check term "own ~writer:Ghost.self location value"
    [ "location"; "value"; "Permission.full"; "Ghost.self" ];
  check term "own ~fraction:Permission.half ~writer:Ghost.self location value"
    [ "location"; "value"; "Permission.half"; "Ghost.self" ];
  check term "own ~writer:Ghost.self ~fraction:Permission.half location value"
    [ "location"; "value"; "Permission.half"; "Ghost.self" ];
  check proof "own ~writer:Ghost.self location value"
    [ "location"; "value"; "Permission.full"; "Ghost.self" ];
  check proof "own ~fraction:Permission.half ~writer:Ghost.self location value"
    [ "location"; "value"; "Permission.half"; "Ghost.self" ];
  check proof "own ~writer:Ghost.self ~fraction:Permission.half location value"
    [ "location"; "value"; "Permission.half"; "Ghost.self" ];
  check_release term "own ~release:Ghost.release location value" "full" "Ghost.release";
  check_release term "own ~fraction:Permission.half ~release:Ghost.release location value"
    "half" "Ghost.release";
  check_release term "own ~release:Ghost.release ~fraction:Permission.half location value"
    "half" "Ghost.release";
  check_release proof "own ~release:Ghost.release location value" "full" "Ghost.release";
  check_release proof
    "own ~fraction:Permission.half ~release:Ghost.release location value" "half"
    "Ghost.release";
  check_release proof
    "own ~release:Ghost.release ~fraction:Permission.half location value" "half"
    "Ghost.release";
  List.iter
    (fun parse ->
      rejected parse
        "own ~fraction:Permission.half ~fraction:Permission.half location value"
        "Duplicate labels on own";
      rejected parse "own ~writer:Ghost.self ~writer:Ghost.self location value"
        "Duplicate labels on own";
      rejected parse "own ~release:Ghost.a ~release:Ghost.b location value"
        "Duplicate labels on own";
      rejected parse "own ~writer:Ghost.self ~release:Ghost.release location value"
        "The ~writer and ~release labels cannot be used together on own";
      rejected parse "own ~release:Ghost.release ~writer:Ghost.self location value"
        "The ~writer and ~release labels cannot be used together on own";
      rejected parse "owns ~writer:Ghost.self location value"
        "Only own accepts labeled arguments";
      rejected parse "owns ~release:Ghost.release location value"
        "Only own accepts labeled arguments")
    [ term; proof ]
