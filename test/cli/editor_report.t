Editor output uses Raven's flags and JSON shapes, with no human-readable prefix.

  $ caravan --manifest > manifest.json
  $ python3 check_editor_report.py manifest manifest.json

  $ caravan --lsp-mode editor_ok.ml > plain.json
  $ python3 check_editor_report.py plain plain.json
  $ caravan --lsp-mode --lsp-annotations editor_ok.ml > enriched.json
  $ python3 check_editor_report.py enriched enriched.json

Verification errors retain Raven's one-based lines and UTF-8 byte columns.

  $ caravan --lsp-mode --lsp-annotations editor_failure.ml > failed.json
  [1]
  $ python3 check_editor_report.py failure failed.json

Compiler errors and warnings stay machine-readable. Trusted warnings preserve success.

  $ caravan --lsp-mode editor_type_error.ml > type.json
  [1]
  $ python3 check_editor_report.py type type.json
  $ caravan --lsp-mode editor_warning.ml > warning.json
  $ python3 check_editor_report.py warning warning.json

All input files are checked after an error.

  $ caravan --lsp-mode editor_type_error.ml editor_failure.ml > multiple.json
  [1]
  $ python3 check_editor_report.py multiple multiple.json

Generated text and editor JSON cannot share standard output.

  $ caravan --lsp-mode --emit-rav editor_ok.ml > conflict.out 2>&1
  [1]
  $ grep -q 'cannot be used together' conflict.out
