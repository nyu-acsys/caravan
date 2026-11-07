Proof steps retain the exact original action range and source-level inline text.
Scope imports, exports and pure bindings stay in the companion proof document.

  $ caravan --lsp-mode --lsp-annotations --lsp-annotations-only editor_proof_steps.ml > steps.json
  $ python3 check_proof_annotations.py steps steps.json

Verification failures retain contracts and proof steps.

  $ caravan --lsp-mode --lsp-annotations editor_proof_failure.ml > failure.json
  [1]
  $ python3 check_proof_annotations.py failure failure.json
