open Base
module C = Caravan_core
module S = Caravan_spec.Spec_ast
module Scopes = C.Proof_scopes

let get = function
  | Ok value -> value
  | Error (error : C.Report.error) -> failwith error.message

let typed source =
  Compmisc.init_path ();
  get
    (C.Signature_contract.compiler ~at:Location.none (fun () ->
         let parsed = Parse.implementation (Lexing.from_string source) in
         let structure, _, _, _, environment =
           Typemod.type_structure (Compmisc.initial_env ()) parsed
         in
         (structure, environment)))

let proof text =
  (Caravan_spec.Spec_parser.proof Caravan_spec.Spec_lexer.token (Lexing.from_string text))
    .declarations

let resolve source text =
  let structure, environment = typed source in
  get (Scopes.resolve ~environment structure (proof text))

let reject source text message =
  let structure, environment = typed source in
  match Scopes.resolve ~environment structure (proof text) with
  | Ok _ -> failwith "Expected a proof-scope error"
  | Error error -> assert (String.is_substring error.message ~substring:message)

let scope inventory namespace =
  Option.value_exn (Scopes.find_namespace inventory namespace)

let local_type scope name =
  get
    (C.Source.ocaml_type scope.Scopes.environment ~at:Location.none
       (S.PTtyapp (Qid (S.mk_id ~loc:Location.none name), [])))

let is_type scope name expected =
  get
    (C.Signature_contract.compiler ~at:Location.none (fun () ->
         Ctype.is_equal scope.Scopes.environment false
           [ local_type scope name ]
           [ expected ]))

let source =
  "module type View = sig type t end\n\
   module Left: View = struct type t = int type hidden = bool end\n\
   module Right = struct type t = bool end\n\
   module Alias = Left\n\
   module type Other = sig type t end\n\
   module Make (Cell: View) () = struct type t = Cell.t end"

let () =
  let inventory =
    resolve source
      "predicate root (x : int) = true\n\
       module Left = struct predicate owned (x : hidden) = true end\n\
       module Right = struct predicate owned (x : t) = true end\n\
       module Make (Cell: View) () = struct predicate owned (x : t) = true end"
  in
  assert (List.length inventory.declarations = 4);
  assert (List.length inventory.scopes = 4);
  assert (Poly.equal inventory.root.namespace []);
  let left = scope inventory [ "Left" ] in
  let right = scope inventory [ "Right" ] in
  assert (not (Scopes.same_scope left right));
  assert (not (Option.equal Path.same left.owner right.owner));
  let left_entry = List.hd_exn (Scopes.declarations_in inventory left) in
  let right_entry = List.hd_exn (Scopes.declarations_in inventory right) in
  assert (String.equal left_entry.name.pid_str right_entry.name.pid_str);
  assert (not (Ident.same left_entry.id right_entry.id));
  assert (is_type left "hidden" Predef.type_bool);
  let public_hidden =
    S.PTtyapp
      ( Qdot (Qid (S.mk_id ~loc:Location.none "Left"), S.mk_id ~loc:Location.none "hidden"),
        [] )
  in
  assert (
    Result.is_error
      (C.Source.ocaml_type inventory.root.environment ~at:Location.none public_hidden));
  assert (is_type right "t" Predef.type_bool);
  assert (Option.is_some left.public_type);
  assert (List.length (scope inventory [ "Make" ]).parameters = 2);
  assert (
    Option.exists (Scopes.find_owner inventory left.owner) ~f:(Scopes.same_scope left))

let () =
  reject source "module Missing = struct end" "No source module definition";
  reject source "module Alias = struct end" "not a module alias";
  reject source "module Left = struct end module Left = struct end"
    "more than one proof block";
  reject source "module Make = struct end" "repeat all source functor parameters";
  reject source "module Make () (Cell: View) = struct end" "parameter kind";
  reject source "module Make (Other: View) () = struct end" "must be named Cell";
  reject source "module Make (Cell: Other) () = struct end"
    "source parameter's module type";
  reject source "module Make (Cell: Missing) () = struct end" "Unknown module type"

let () =
  let source =
    "module Left = struct module type VIEW = sig type t end end\n\
     module Right = struct module type VIEW = sig type t end end\n\
     module Make (Cell: Left.VIEW) = struct end"
  in
  let inventory = resolve source "module Make (Cell: Left.VIEW) = struct end" in
  assert (List.length (scope inventory [ "Make" ]).parameters = 1);
  reject source "module Make (Cell: Right.VIEW) = struct end"
    "source parameter's module type"

let () =
  let inventory =
    resolve
      "module Outer = struct\n\
       module Child = struct type t = int end\n\
       module Other = struct type t = bool end end"
      "module Outer = struct\n\
       module Child = struct predicate owned (x : t) = true end\n\
       module Other = struct predicate owned (x : t) = true end end"
  in
  let outer = scope inventory [ "Outer" ] in
  let child = scope inventory [ "Outer"; "Child" ] in
  assert (Option.equal Path.same child.parent outer.owner);
  assert (is_type child "t" Predef.type_int);
  assert (is_type (scope inventory [ "Outer"; "Other" ]) "t" Predef.type_bool)

let () =
  let inventory =
    resolve
      "module M = struct type t = int end\n\
       module Outer = struct module M = struct type t = bool end end"
      "module M = struct predicate owned (x : t) = true end\n\
       module Outer = struct\n\
       module M = struct predicate owned (x : t) = true end end"
  in
  let original = scope inventory [ "M" ] in
  let outer = scope inventory [ "Outer" ] in
  let final = scope inventory [ "Outer"; "M" ] in
  assert (is_type original "t" Predef.type_int);
  assert (is_type final "t" Predef.type_bool);
  assert (not (Scopes.same_scope original final));
  let declared =
    List.filter_map outer.structure.str_items ~f:(fun item ->
        match item.Typedtree.str_desc with
        | Tstr_module { mb_id = Some id; _ } -> Some id
        | _ -> None)
  in
  assert (Option.equal Ident.same final.declaration_id (List.last declared))
