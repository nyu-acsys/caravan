(** Raven-compatible editor diagnostics; lines are one-based and columns are byte offsets.
*)

open Base
module R = Raven_api

let location ~fallback at =
  let start = R.Loc.start at and stop = R.Loc.stop at in
  let file = if String.is_empty start.pos_fname then fallback else start.pos_fname in
  [
    ("file", `String file);
    ("start_line", `Int (Int.max 1 start.pos_lnum));
    ("start_col", `Int (Int.max 0 (start.pos_cnum - start.pos_bol)));
    ("end_line", `Int (Int.max 1 stop.pos_lnum));
    ("end_col", `Int (Int.max 0 (stop.pos_cnum - stop.pos_bol)));
  ]

let entry ~fallback ~kind at message : Yojson.Basic.t =
  `Assoc
    (location ~fallback at
    @ [
        ("kind", `String kind);
        ( "message",
          `List
            (String.split message ~on:'\n'
            |> List.filter ~f:(fun line -> not (String.is_empty line))
            |> List.map ~f:(fun line -> `String line)) );
      ])

let diagnostic ~fallback (d : R.Diagnostic.t) =
  let kind =
    match d.severity with
    | Warning -> "Warning"
    | Error -> (
        match d.kind with
        | Syntax -> "Syntax"
        | Type -> "Type"
        | Verification -> "Verification"
        | Unsupported -> "Unsupported"
        | Internal -> "Internal"
        | Other -> "Generic")
  in
  entry ~fallback ~kind d.loc d.message
  :: List.map d.related ~f:(fun related ->
      entry ~fallback ~kind:"RelatedLoc" related.related_loc related.related_message)

let contract ~fallback (a : Caravan_core.Editor_annotations.contract) =
  `Assoc
    (location ~fallback (Caravan_core.Report.loc a.loc)
    @ [
        ("kind", `String "InheritedContract");
        ("source", `String a.source);
        ("source_loc", `Assoc (location ~fallback (Caravan_core.Report.loc a.source_loc)));
        ( "clauses",
          `List
            (List.map a.clauses ~f:(fun clause ->
                 `Assoc
                   ([ ("keyword", `String clause.keyword); ("text", `String clause.text) ]
                   @ location ~fallback (Caravan_core.Report.loc clause.loc)))) );
      ])

let annotation ~fallback = function
  | Caravan_core.Editor_annotations.Contract a -> contract ~fallback a
  | Proof_step a ->
      `Assoc
        (location ~fallback (Caravan_core.Report.loc a.loc)
        @ [
            ("kind", `String "ProofStep");
            ( "source_loc",
              `Assoc (location ~fallback (Caravan_core.Report.loc a.source_loc)) );
            ("text", `String a.text);
          ])

let member ~fallback (m : Caravan_core.Editor_members.member) =
  let status s = `String (Caravan_core.Editor_members.status_to_string s) in
  `Assoc
    (location ~fallback (Caravan_core.Report.loc m.name_loc)
    @ [
        ("id", `String m.id);
        ("name", `String m.name);
        ("kind", `String m.kind);
        ("extent", `Assoc (location ~fallback (Caravan_core.Report.loc m.extent)));
        ("group", `Bool m.group);
        ("status", status m.status);
        ("own_status", status m.own_status);
        ("own_checks", `Int (List.length m.checks));
        ( "counts",
          `Assoc
            (List.map m.counts ~f:(fun (s, n) ->
                 (Caravan_core.Editor_members.status_to_string s, `Int n))) );
      ]
    @ Option.value_map m.parent ~default:[] ~f:(fun id -> [ ("parent", `String id) ]))

let report ~annotations (results : Caravan_core.Check.result list) : Yojson.Basic.t =
  let errors =
    `List
      (List.concat_map results ~f:(fun result ->
           List.concat_map result.diagnostics ~f:(diagnostic ~fallback:result.file)))
  in
  if not annotations then errors
  else
    `Assoc
      [
        ("errors", errors);
        ( "annotations",
          `List
            (List.concat_map results ~f:(fun result ->
                 List.map result.annotations ~f:(annotation ~fallback:result.file))) );
        ( "members",
          `List
            (List.concat_map results ~f:(fun result ->
                 List.map result.members ~f:(member ~fallback:result.file))) );
        ("references", `List []);
        ("symbols", `List []);
        ( "dependencies",
          `List
            (List.concat_map results ~f:(fun result -> result.dependencies)
            |> List.dedup_and_sort ~compare:String.compare
            |> List.map ~f:(fun file -> `String file)) );
      ]

let to_string ~annotations results = Yojson.Basic.to_string (report ~annotations results)

let manifest ~version ~lsp_protocol ~min_z3 =
  Yojson.Basic.to_string
    (`Assoc
       [
         ("version", `String version);
         ("lsp_protocol", `Int lsp_protocol);
         ("min_z3", `String min_z3);
         ("ocaml_version", `String Stdlib.Sys.ocaml_version);
         ("raven_api_version", `Int R.version);
       ])
