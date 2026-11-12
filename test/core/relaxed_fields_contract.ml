open Base
(** Relaxed reads preserve past-write provenance without requiring the latest value. *)

module R = Raven_api
module P = Caravan_core.Prelude
module F = Caravan_core.Relaxed_fields_contract
module E = Caravan_core.Execution_contract

let loc = R.Loc.none
let ident = R.Ident.make ~loc
let name = R.Name.make ~loc
let variable text = R.Expr.var ~loc (name text)
let integer = R.Type.int ~loc
let reference = R.Type.ref ~loc
let int value = R.Expr.int ~loc value
let entry event value = R.Expr.tuple ~loc [ event; value ]
let binary = R.Expr.binary ~loc
let entries first second = R.Expr.set ~loc [ entry first (int 0); entry second (int 1) ]

let call ?(field = "Cell") text arguments =
  R.Expr.call ~loc (R.Name.make ~loc ~path:[ field ] text) arguments

let local ?(ghost = false) text typ = R.Stmt.local ~loc ~ghost ~typ (ident text)

let assign targets expression =
  [ R.Stmt.assign ~loc (List.map targets ~f:variable) (R.Stmt.expr_rhs expression) ]

let invoke expression = R.Stmt.call ~loc expression
let assert_ expression = R.Stmt.assert_ ~loc (R.Spec.make expression)

let tag text typ =
  R.Member.module_ ~loc
    ~implements:[ (R.Name.make ~loc ~path:[ "Library" ] "Type", []) ]
    (ident text)
    [ R.Member.type_ ~loc ~rep:true (ident "T") (Some typ) ]

let instance text tag =
  R.Member.instance ~loc
    ~def:
      ( name F.module_name,
        [ R.Type.named ~loc (name tag) []; R.Type.named ~loc (name "Value") [] ] )
    (ident text) (name F.module_name)

let support =
  P.value_signature
  :: (P.value_dictionary ~loc ~name:"Value" ~carrier:integer
        ~unrestricted:(R.Expr.bool ~loc false)
        ~body:(binary Geq (variable "value") (int 0))
      :: E.support ~loc ~mutex:false ~visibility:true ()
     @ F.support ~loc ()
     @ [
         tag "FirstTag" integer;
         tag "SecondTag" (R.Type.bool ~loc);
         instance "Cell" "FirstTag";
         instance "OtherCell" "SecondTag";
         R.Member.instance ~loc
           ~def:
             ( R.Name.make ~loc ~path:[ E.module_name ] "Atomic",
               [ R.Type.named ~loc (name "Value") [] ] )
           (ident "Channel")
           (R.Name.make ~loc ~path:[ E.module_name ] "AtomicSignature");
       ])

type probe =
  | Valid
  | Latest
  | Future
  | Wrong_location
  | Wrong_field
  | No_state
  | Invalid_write
  | No_acquire
  | Published_valid
  | Adopted_valid
  | Missing_publication_acquire
  | Foreign_publisher
  | Unordered_private_history
  | Repeat_publication
  | Published_latest
  | Plain_after_publication

let client probe =
  let cell = variable "cell"
  and first = variable "first"
  and second = variable "second" in
  let result = variable "result" and selected = variable "selected" in
  let initial = R.Expr.set ~loc [ entry first (int 0) ] in
  let metadata args =
    args
    @ [
        R.Expr.set ~loc [];
        R.Expr.null ~loc;
        R.Expr.tuple ~loc [ R.Expr.bool ~loc true; variable "writer" ];
      ]
  in
  let read value stamp journal =
    assign [ "result"; "selected" ]
      (call "read" (metadata [ cell; value; stamp; journal ]))
  in
  let write value =
    assign [ "second" ]
      (call "write" (metadata [ variable "writer"; cell; value; int 0; first; initial ]))
  in
  let statements =
    local ~ghost:true "writer" reference
    @ assign [ "writer" ] (E.start ~loc)
    @ local "cell" reference
    @ local ~ghost:true "first" reference
    @ local ~ghost:true "second" reference
    @ local "result" integer
    @ local ~ghost:true "selected" reference
    @ assign [ "cell"; "first" ] (call "make" [ variable "writer"; int 0 ])
    @
    match probe with
    | Adopted_valid ->
        let writer = variable "writer" and reader = variable "reader" in
        let channel method_ arguments =
          R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Channel" ] method_) arguments
        in
        local ~ghost:true "reader" reference
        @ local ~ghost:true "cut" reference
        @ local ~ghost:true "third" reference
        @ local "channel" reference
        @ local ~ghost:true "released" (Caravan_core.Visibility_contract.view_type ~loc)
        @ local ~ghost:true "prior" (Caravan_core.Visibility_contract.view_type ~loc)
        @ assign [ "reader" ] (E.start ~loc)
        @ write (int 1)
        @ assign [ "prior" ]
            (Caravan_core.Visibility_contract.reconcile ~loc ~module_name:E.module_name
               writer (R.Expr.set ~loc [ second ]))
        @ assign [ "channel"; "released" ]
            (channel "make" [ writer; variable "prior"; int 1 ])
        @ assign [ "result" ] (channel "get" [ reader; variable "channel" ])
        @ [
            invoke
              (Caravan_core.Visibility_contract.weaken ~loc ~module_name:E.module_name
                 reader (variable "released") (R.Expr.set ~loc [ second ]));
            invoke (call "adopt" [ reader; cell; R.Expr.bool ~loc true ]);
          ]
        @ assign [ "third" ] (call "write" [ reader; cell; int 2 ])
        @ assign [ "cut" ] (call "publish" [ reader; cell; R.Expr.bool ~loc true ])
        @ assign [ "result"; "selected" ] (call "read_published" [ reader; cell ])
        @ [ assert_ (binary Eq result (int 2)) ]
    | Published_valid | Missing_publication_acquire | Foreign_publisher
    | Repeat_publication | Published_latest | Plain_after_publication
    | Unordered_private_history ->
        let writer = variable "writer" and reader = variable "reader" in
        let cut = variable "cut" and third = variable "third" in
        let all =
          R.Expr.set ~loc
            [ entry first (int 0); entry second (int 1); entry third (int 2) ]
        in
        let published_entries =
          R.Expr.set ~loc [ entry second (int 1); entry third (int 2) ]
        in
        let channel method_ arguments =
          R.Expr.call ~loc (R.Name.make ~loc ~path:[ "Channel" ] method_) arguments
        in
        local ~ghost:true "reader" reference
        @ local ~ghost:true "cut" reference
        @ local ~ghost:true "third" reference
        @ local "channel" reference
        @ local ~ghost:true "released" (Caravan_core.Visibility_contract.view_type ~loc)
        @ local ~ghost:true "prior" (Caravan_core.Visibility_contract.view_type ~loc)
        @ assign [ "reader" ] (E.start ~loc)
        @ write (int 1)
        @ (if Poly.equal probe Unordered_private_history then
             assign [ "third" ] (call "write" [ reader; cell; int 2 ])
             @ assign [ "third" ] (call "write" [ writer; cell; int 3 ])
           else [])
        @ assign [ "cut" ]
            (call "publish"
               [
                 (if Poly.equal probe Foreign_publisher then reader else writer);
                 cell;
                 R.Expr.bool ~loc true;
               ])
        @
        if
          Poly.equal probe Foreign_publisher || Poly.equal probe Unordered_private_history
        then []
        else if Poly.equal probe Repeat_publication then
          assign [ "cut" ] (call "publish" [ writer; cell; R.Expr.bool ~loc true ])
        else
          assign [ "third" ] (call "write" [ writer; cell; int 2 ])
          @ (if
               Poly.equal probe Missing_publication_acquire
               || Poly.equal probe Plain_after_publication
             then []
             else
               assign [ "prior" ] (call "release" [ writer; cell; R.Expr.bool ~loc true ])
               @ assign [ "channel"; "released" ]
                   (channel "make" [ writer; variable "prior"; int 1 ])
               @ assign [ "result" ] (channel "get" [ reader; variable "channel" ])
               @ [
                   invoke
                     (call "acquire"
                        [ reader; cell; R.Expr.bool ~loc true; variable "released" ]);
                 ])
          @ assign [ "result"; "selected" ]
              (if Poly.equal probe Plain_after_publication then call "read" [ cell ]
               else call "read_published" [ reader; cell ])
          @ [
              assert_
                (if Poly.equal probe Published_latest then binary Eq result (int 2)
                 else binary Or (binary Eq result (int 1)) (binary Eq result (int 2)));
            ]
          @ [
              invoke
                (call "reconcile"
                   [
                     cell;
                     R.Expr.bool ~loc true;
                     first;
                     int 0;
                     int 2;
                     third;
                     all;
                     published_entries;
                     cut;
                     R.Expr.tuple ~loc [ R.Expr.bool ~loc true; writer ];
                   ]);
            ]
    | Future ->
        read (int 0) first initial
        @ write (int 1)
        @ [ assert_ (binary Eq result (int 1)) ]
    | No_acquire ->
        local ~ghost:true "owner" reference
        @ assign [ "owner" ] (E.start ~loc)
        @ read (int 0) first initial
        @ [
            assert_
              (Caravan_core.Visibility_contract.seen ~loc ~module_name:E.module_name
                 (variable "owner") (R.Expr.set ~loc [ cell ]));
          ]
    | No_state ->
        [
          R.Stmt.exhale ~loc
            (R.Spec.make (call "state" (metadata [ cell; int 0; first; initial ])));
        ]
        @ read (int 0) first initial
    | Wrong_location ->
        local "other" reference
        @ local ~ghost:true "other_first" reference
        @ assign [ "other"; "other_first" ] (call "make" [ variable "writer"; int 0 ])
        @ [
            invoke
              (call "reconcile"
                 [
                   variable "other";
                   R.Expr.bool ~loc true;
                   first;
                   int 0;
                   int 0;
                   variable "other_first";
                   R.Expr.set ~loc [ entry (variable "other_first") (int 0) ];
                   R.Expr.set ~loc [];
                   R.Expr.null ~loc;
                   R.Expr.tuple ~loc [ R.Expr.bool ~loc true; variable "writer" ];
                 ]);
          ]
    | Wrong_field ->
        [
          invoke
            (call ~field:"OtherCell" "reconcile"
               (metadata
                  [ cell; R.Expr.bool ~loc true; first; int 0; int 0; first; initial ]));
        ]
    | Invalid_write -> write (int (-1))
    | Valid | Latest ->
        read (int 0) first initial
        @ [
            assert_ (binary Eq result (int 0));
            invoke (call "duplicate" [ cell; R.Expr.bool ~loc true; selected; result ]);
          ]
        @ write (int 1)
        @ [
            invoke
              (call "reconcile"
                 [
                   cell;
                   R.Expr.bool ~loc true;
                   selected;
                   result;
                   int 1;
                   second;
                   entries first second;
                   R.Expr.set ~loc [];
                   R.Expr.null ~loc;
                   R.Expr.tuple ~loc [ R.Expr.bool ~loc true; variable "writer" ];
                 ]);
          ]
        @ read (int 1) second (entries first second)
        @ [
            assert_
              (match probe with
              | Valid -> binary Or (binary Eq result (int 0)) (binary Eq result (int 1))
              | _ -> binary Eq result (int 1));
          ]
  in
  R.Member.callable (R.Callable.proc ~loc (ident "client") (Some statements))

let check probe =
  let result = R.verify (R.Program.make ~loc (support @ [ client probe ])) in
  if List.mem [ Valid; Published_valid; Adopted_valid ] probe ~equal:Poly.equal then (
    if not result.verified then
      failwith
        (String.concat ~sep:"\n" (List.map result.diagnostics ~f:R.Diagnostic.to_string)))
  else (
    assert (not result.verified);
    assert (
      List.for_all result.diagnostics ~f:(fun diagnostic ->
          not
            (String.is_substring
               (String.lowercase (R.Diagnostic.to_string diagnostic))
               ~substring:"timeout")));
    assert (
      List.exists result.diagnostics ~f:(fun diagnostic ->
          List.mem
            [ Some R.Diagnostic.Precondition; Some R.Diagnostic.Assertion ]
            diagnostic.R.Diagnostic.code ~equal:Poly.equal)))

let () =
  List.iter
    [
      Valid;
      Latest;
      Future;
      Wrong_location;
      Wrong_field;
      No_state;
      Invalid_write;
      No_acquire;
      Published_valid;
      Adopted_valid;
      Missing_publication_acquire;
      Foreign_publisher;
      Unordered_private_history;
      Repeat_publication;
      Published_latest;
      Plain_after_publication;
    ]
    ~f:check
