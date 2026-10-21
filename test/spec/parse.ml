(* Parses contracts and prints their structure. *)

open Caravan_spec
open Spec_ast

let rec qualid = function
  | Qid id -> id.pid_str
  | Qdot (q, id) -> qualid q ^ "." ^ id.pid_str

let constant = function
  | Pconst_integer (n, _) -> n
  | Pconst_char c -> Printf.sprintf "%C" c
  | Pconst_string (s, _) -> Printf.sprintf "%S" s
  | Pconst_float f -> f

let rec pat p =
  match p.pat_desc with
  | Pwild -> "_"
  | Pid id -> id.pid_str
  | Ptuple ps -> "(tuple " ^ String.concat " " (List.map pat ps) ^ ")"
  | Pcast (p, _) -> "(cast " ^ pat p ^ ")"
  | Pconstr (c, None) -> qualid c
  | Pconstr (c, Some p) -> "(" ^ qualid c ^ " " ^ pat p ^ ")"
  | Pconst c -> constant c

let rec term t =
  match t.term_desc with
  | Ttrue -> "true"
  | Tfalse -> "false"
  | Tconst c -> constant c
  | Tvar q -> qualid q
  | Tfield (t, q) -> "(field " ^ term t ^ " " ^ qualid q ^ ")"
  | Tapply (f, a) -> "(" ^ term f ^ " " ^ term a ^ ")"
  | Tinfix (a, o, b) -> "(infix " ^ term a ^ " " ^ o.pid_str ^ " " ^ term b ^ ")"
  | Tif (c, a, b) -> "(if " ^ term c ^ " " ^ term a ^ " " ^ term b ^ ")"
  | Tquant (q, bs, t) ->
      let q = match q with Tforall -> "forall" | Texists -> "exists" in
      let b (id, ty) = id.pid_str ^ match ty with Some _ -> ":ty" | None -> "" in
      "(" ^ q ^ " " ^ String.concat " " (List.map b bs) ^ ". " ^ term t ^ ")"
  | Tattr (a, t) -> "(attr " ^ a ^ " " ^ term t ^ ")"
  | Tlet (p, a, b) -> "(let " ^ pat p ^ " " ^ term a ^ " " ^ term b ^ ")"
  | Tmatch (t, cases) ->
      let case (p, t) = "[" ^ pat p ^ " -> " ^ term t ^ "]" in
      "(match " ^ term t ^ " " ^ String.concat " " (List.map case cases) ^ ")"
  | Tcast (t, _) -> "(cast " ^ term t ^ ")"
  | Ttuple ts -> "(tuple " ^ String.concat " " (List.map term ts) ^ ")"
  | Told t -> "(old " ^ term t ^ ")"

let arg = function
  | Lwild -> "_"
  | Lunit _ -> "()"
  | Lvar id -> id.pid_str
  | Lghost (id, _) -> "[" ^ id.pid_str ^ "]"

let parse text =
  print_endline ("> " ^ String.trim text);
  let lexbuf = Lexing.from_string text in
  match Spec_parser.contract Spec_lexer.token lexbuf with
  | c ->
      Option.iter
        (fun h ->
          Printf.printf "header %s = %s %s\n"
            (String.concat ", " (List.map arg h.hd_ret))
            h.hd_name.pid_str
            (String.concat " " (List.map arg h.hd_args)))
        c.header;
      List.iter (fun t -> print_endline ("requires " ^ term t)) c.requires;
      List.iter (fun t -> print_endline ("ensures " ^ term t)) c.ensures;
      List.iter (fun t -> print_endline ("variant " ^ term t)) c.variant;
      if c.pure then print_endline "pure"
  | exception Spec_parser.Error ->
      Printf.printf "syntax error at %d\n" (Lexing.lexeme_start lexbuf)
  | exception Spec_lexer.Error (_, message) -> print_endline ("lexing error: " ^ message)

let () =
  List.iter parse
    [
      "r = abs x requires x > min_int ensures r >= 0 ensures r = x || r = -x";
      "q, r = div [k : int] x y requires 0 <= x < y ensures x = q * y + r";
      "requires a -> b <-> not c ensures forall i: int. 0 <= i -> f i >= old (f i)";
      "n = length l ensures n = match l with [] -> 0 | _ :: t -> 1 + length t variant l";
      {|v = f x ensures match x with
         | Some (a, b) -> a = b
         | None -> match y with A -> true | B -> false|};
      "ensures let (a, b) = p in a + b = 3 && t.next = None pure";
      "ensures exists x y. x * y = 4";
      "ensures r = Some [x; y] && l = [] && f [1] = x :: l";
      "ensures x = 1 +";
      "ensures x { y";
    ]
