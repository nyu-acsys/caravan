(** Native field attributes select one discipline without changing alias identity. *)

open Base
module C = Caravan_core
module D = C.Field_disciplines

let get = function
  | Ok value -> value
  | Error (error : C.Report.error) -> failwith error.message

let attribute ?(payload = Parsetree.PStr []) text =
  Ast_helper.Attr.mk { txt = text; loc = Location.none } payload

let parse attributes = get (D.parse_attributes attributes)

let structure text =
  Compmisc.init_path ();
  get
    (C.Signature_contract.compiler ~at:Location.none (fun () ->
         let parsed = Parse.implementation (Lexing.from_string text) in
         let typed, _, _, _, _ =
           Typemod.type_structure (Compmisc.initial_env ()) parsed
         in
         typed))

let signature text =
  Compmisc.init_path ();
  get
    (C.Signature_contract.compiler ~at:Location.none (fun () ->
         let parsed = Parse.interface (Lexing.from_string text) in
         Typemod.type_interface (Compmisc.initial_env ()) parsed))

let count fields kind =
  List.count fields ~f:(fun (field : D.t) -> Poly.equal field.kind kind)

let () =
  assert (Option.is_none (parse []));
  assert (Result.is_error (D.parse_attributes [ attribute "caravan.history" ]));
  assert (Poly.equal (parse [ attribute "caravan.frozen" ]) (Some D.Frozen));
  assert (Poly.equal (parse [ attribute "caravan.relaxed" ]) (Some D.Relaxed));
  assert (Option.is_none (parse [ attribute "frozen"; attribute "relaxed" ]));
  assert (
    Poly.equal
      (parse [ attribute "third_party"; attribute "caravan.frozen" ])
      (Some D.Frozen));
  assert (
    Result.is_error
      (D.parse_attributes [ attribute "caravan.frozen"; attribute "caravan.frozen" ]));
  assert (
    Result.is_error
      (D.parse_attributes [ attribute "caravan.frozen"; attribute "caravan.relaxed" ]));
  let payload =
    Parsetree.PStr
      [ Ast_helper.Str.eval (Ast_helper.Exp.constant (Ast_helper.Const.integer "1")) ]
  in
  assert (Result.is_error (D.parse_attributes [ attribute ~payload "caravan.frozen" ]))

let () =
  let typed =
    structure
      {|type node = {
          mutable frozen : int [@caravan.frozen];
          mutable past : bool [@caravan.relaxed];
          mutable ordinary : int [@history];
          immutable : bool;
        }
        type alias = node
        type 'a box = { mutable value : 'a [@caravan.frozen] }
        type variant = Node of { mutable payload : int [@caravan.relaxed] }
        module Nested = struct
          type t = { mutable value : int [@caravan.frozen] }
        end|}
  in
  let fields = get (D.collect_structure typed) in
  assert (List.length fields = 7);
  assert (count fields D.Frozen = 3);
  assert (count fields D.Relaxed = 2);
  assert (count fields D.Ordinary = 2);
  assert (List.count fields ~f:(fun field -> field.D.immutable) = 1);
  let canonical = Path.Pident (Ident.create_local "Canonical") in
  let single = structure {|type t = { mutable value : int [@caravan.frozen] }|} in
  match get (D.collect_structure ~canonicalize:(fun _ -> canonical) single) with
  | [ field ] -> assert (Path.same field.D.record_path canonical)
  | _ -> failwith "Expected one canonicalized field"

let () =
  let typed =
    signature
      {|type t = {
          mutable frozen : int [@caravan.frozen];
          mutable ordinary : int;
        }
        module Nested : sig
          type t = { mutable value : int [@caravan.relaxed] }
        end
        module type CELL = sig
          type t = { mutable value : int [@caravan.frozen] }
        end|}
  in
  let fields = get (D.collect_signature typed) in
  assert (List.length fields = 4);
  assert (count fields D.Frozen = 2);
  assert (count fields D.Relaxed = 1);
  assert (count fields D.Ordinary = 1)

let () =
  let immutable = structure {|type t = { value : int [@caravan.frozen] }|} in
  assert (Result.is_error (D.collect_structure immutable))

let () =
  let fields =
    get
      (D.collect_structure
         (structure {|type t = { mutable count : int; next : int Atomic.t }|}))
  in
  assert (List.length fields = 2);
  assert (not (D.shared fields));
  assert (
    List.exists fields ~f:(fun field ->
        field.D.immutable && String.equal field.label "next"))

let () =
  let fields =
    get
      (D.collect_structure
         (structure "type t = { mutable value : bool [@caravan.relaxed] [@caravan.raw] }"))
  in
  let raw = List.hd_exn fields in
  assert raw.raw;
  assert (
    match Types.get_desc (D.storage_type raw) with
    | Tconstr (path, [ _ ], _) -> Path.same path Predef.path_option
    | _ -> false);
  let ordinary = { raw with raw = false } in
  assert (Result.is_error (D.check ~at:Location.none ~expected:ordinary ~actual:raw));
  assert (Result.is_error (D.check ~at:Location.none ~expected:raw ~actual:ordinary));
  assert (Result.is_error (D.parse_raw ~kind:(Some D.Frozen) [ attribute "caravan.raw" ]));
  assert (
    Result.is_error
      (D.parse_raw ~kind:(Some D.Relaxed)
         [
           attribute
             ~payload:
               (PStr
                  [
                    Ast_helper.Str.eval
                      (Ast_helper.Exp.constant (Ast_helper.Const.integer "1"));
                  ])
             "caravan.raw";
         ]))
