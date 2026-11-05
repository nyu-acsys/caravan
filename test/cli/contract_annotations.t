Contracts are attached by the front end, including nested signatures and functors.
Original parameter names, clause kinds, source text and UTF-8 byte ranges survive.

  $ caravan --lsp-mode --lsp-annotations --lsp-annotations-only editor_contracts.ml > contracts.json
  $ python3 check_contract_annotations.py contracts contracts.json
  $ caravan --lsp-mode --lsp-annotations --lsp-annotations-only editor_functor_contract.ml > functor.json
  $ python3 check_contract_annotations.py functor functor.json

Proof headers point into the original proof file, despite their implementation anchor.

  $ caravan --lsp-mode --lsp-annotations --lsp-annotations-only editor_proof_contract.ml > proof.json
  $ python3 check_contract_annotations.py proof proof.json

CRLF proof headers preserve their multiline source text and byte ranges.

  $ cp editor_proof_contract.ml editor_proof_crlf.ml
  $ python3 -c 'from pathlib import Path; source = Path("editor_proof_contract.proof").read_bytes(); Path("editor_proof_crlf.proof").write_bytes(source.replace(b"\r\n", b"\n").replace(b"\n", b"\r\n"))'
  $ caravan --lsp-mode --lsp-annotations --lsp-annotations-only editor_proof_crlf.ml > proof_crlf.json
  $ python3 check_contract_annotations.py proof proof_crlf.json

Annotation discovery works without a solver on PATH on Unix. Windows keeps PATH for
native DLL loading. Inline contracts are excluded on every platform.

  $ python3 check_contract_annotations.py no-solver contracts.json
  $ caravan --lsp-mode --lsp-annotations --lsp-annotations-only editor_ok.ml > inline.json
  $ python3 check_contract_annotations.py inline inline.json

Verification failure retains its attached contract. Attachment failures report errors.

  $ caravan --lsp-mode --lsp-annotations editor_contract_failure.ml > failed.json
  [1]
  $ python3 check_contract_annotations.py failure failed.json
  $ caravan --lsp-mode --lsp-annotations --lsp-annotations-only editor_contract_alias.ml > alias.json
  [1]
  $ python3 check_contract_annotations.py alias alias.json
  $ caravan --lsp-mode --lsp-annotations --lsp-annotations-only editor_contract_value.ml > value.json
  [1]
  $ python3 check_contract_annotations.py value value.json
  $ caravan --lsp-mode --lsp-annotations --lsp-annotations-only editor_contract_mismatch.ml > mismatch.json
  [1]
  $ python3 check_contract_annotations.py mismatch mismatch.json
  $ caravan --lsp-mode --lsp-annotations --lsp-annotations-only editor_type_error.ml > type.json
  [1]
  $ python3 check_contract_annotations.py type type.json
